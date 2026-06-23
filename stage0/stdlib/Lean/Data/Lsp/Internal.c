// Lean compiler output
// Module: Lean.Data.Lsp.Internal
// Imports: public import Lean.Data.Lsp.Basic public import Lean.Data.JsonRpc public import Lean.Data.DeclarationRange public import Init.Data.Array.GetLit import Init.Omega
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_List_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__4_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "m"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(165, 239, 73, 172, 230, 126, 139, 134)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__7_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__9_value;
static const lean_array_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__7_value),((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__9_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__10_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11_value;
static const lean_string_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(14, 215, 4, 153, 96, 18, 167, 14)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__13_value;
static const lean_array_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__7_value),((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__13_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__14_value)}};
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr = (const lean_object*)&l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_RefIdent_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_RefIdent_instFromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_RefIdent_instFromJson = (const lean_object*)&l_Lean_Lsp_RefIdent_instFromJson___closed__0_value;
static const lean_closure_object l_Lean_Lsp_RefIdent_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_RefIdent_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Lsp_instToJsonRefInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__3_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__2_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRefInfo___lam__1, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__3_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonRefInfo___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRefInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionModuleRefs___aux__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionModuleRefs;
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__0_value),((lean_object*)&l_Lean_Lsp_instToJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonModuleRefs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleRefs___lam__3, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__2_value),((lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instToJsonModuleRefs___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonModuleRefs = (const lean_object*)&l_Lean_Lsp_instToJsonModuleRefs___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleRefs___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleRefs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleRefs___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value),((lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonModuleRefs___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonModuleRefs = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanIleanInfoParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renamed"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "allExcept"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 171, 189, 33, 127, 223, 44, 88)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exceptions"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(192, 220, 58, 79, 173, 93, 125, 104)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value;
static const lean_array_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__5_value),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__7_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__8_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "from"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(51, 132, 19, 107, 10, 182, 190, 14)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11_value;
static const lean_string_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "to"};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(203, 162, 13, 215, 195, 228, 231, 139)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value;
static const lean_array_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__11_value),((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__13_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__14_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonOpenNamespace_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonOpenNamespace = (const lean_object*)&l_Lean_Lsp_instFromJsonOpenNamespace___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonOpenNamespace_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonOpenNamespace___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonOpenNamespace = (const lean_object*)&l_Lean_Lsp_instToJsonOpenNamespace___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx(lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_unsigned_to_nat(0u);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_unsigned_to_nat(1u);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorIdx___boxed(lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Lsp_RefIdent_ctorIdx(v_x_103_);
lean_dec_ref(v_x_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___redArg(lean_object* v_t_105_, lean_object* v_k_106_){
_start:
{
lean_object* v_moduleName_107_; lean_object* v_identName_108_; lean_object* v___x_109_; 
v_moduleName_107_ = lean_ctor_get(v_t_105_, 0);
lean_inc_ref(v_moduleName_107_);
v_identName_108_ = lean_ctor_get(v_t_105_, 1);
lean_inc_ref(v_identName_108_);
lean_dec_ref(v_t_105_);
v___x_109_ = lean_apply_2(v_k_106_, v_moduleName_107_, v_identName_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim(lean_object* v_motive_110_, lean_object* v_ctorIdx_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_112_, v_k_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_ctorElim___boxed(lean_object* v_motive_116_, lean_object* v_ctorIdx_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_k_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Lsp_RefIdent_ctorElim(v_motive_116_, v_ctorIdx_117_, v_t_118_, v_h_119_, v_k_120_);
lean_dec(v_ctorIdx_117_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim___redArg(lean_object* v_t_122_, lean_object* v_const_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_122_, v_const_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_const_elim(lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_const_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_126_, v_const_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim___redArg(lean_object* v_t_130_, lean_object* v_fvar_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_130_, v_fvar_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fvar_elim(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_fvar_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Lsp_RefIdent_ctorElim___redArg(v_t_134_, v_fvar_136_);
return v___x_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v_b_143_; lean_object* v_b_144_; 
if (lean_obj_tag(v_x_138_) == 0)
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_moduleName_147_; lean_object* v_identName_148_; lean_object* v_moduleName_149_; lean_object* v_identName_150_; 
v_moduleName_147_ = lean_ctor_get(v_x_138_, 0);
v_identName_148_ = lean_ctor_get(v_x_138_, 1);
v_moduleName_149_ = lean_ctor_get(v_x_139_, 0);
v_identName_150_ = lean_ctor_get(v_x_139_, 1);
v_a_141_ = v_moduleName_147_;
v_a_142_ = v_identName_148_;
v_b_143_ = v_moduleName_149_;
v_b_144_ = v_identName_150_;
goto v___jp_140_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
else
{
if (lean_obj_tag(v_x_139_) == 1)
{
lean_object* v_moduleName_152_; lean_object* v_id_153_; lean_object* v_moduleName_154_; lean_object* v_id_155_; 
v_moduleName_152_ = lean_ctor_get(v_x_138_, 0);
v_id_153_ = lean_ctor_get(v_x_138_, 1);
v_moduleName_154_ = lean_ctor_get(v_x_139_, 0);
v_id_155_ = lean_ctor_get(v_x_139_, 1);
v_a_141_ = v_moduleName_152_;
v_a_142_ = v_id_153_;
v_b_143_ = v_moduleName_154_;
v_b_144_ = v_id_155_;
goto v___jp_140_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
v___jp_140_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_string_dec_eq(v_a_141_, v_b_143_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_string_dec_eq(v_a_142_, v_b_144_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRefIdent_beq___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Lsp_instBEqRefIdent_beq(v_x_157_, v_x_158_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v_x_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRefIdent_hash(lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_moduleName_164_; lean_object* v_identName_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; 
v_moduleName_164_ = lean_ctor_get(v_x_163_, 0);
v_identName_165_ = lean_ctor_get(v_x_163_, 1);
v___x_166_ = 0ULL;
v___x_167_ = lean_string_hash(v_moduleName_164_);
v___x_168_ = lean_uint64_mix_hash(v___x_166_, v___x_167_);
v___x_169_ = lean_string_hash(v_identName_165_);
v___x_170_ = lean_uint64_mix_hash(v___x_168_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_moduleName_171_; lean_object* v_id_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; 
v_moduleName_171_ = lean_ctor_get(v_x_163_, 0);
v_id_172_ = lean_ctor_get(v_x_163_, 1);
v___x_173_ = 1ULL;
v___x_174_ = lean_string_hash(v_moduleName_171_);
v___x_175_ = lean_uint64_mix_hash(v___x_173_, v___x_174_);
v___x_176_ = lean_string_hash(v_id_172_);
v___x_177_ = lean_uint64_mix_hash(v___x_175_, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent_hash___boxed(lean_object* v_x_178_){
_start:
{
uint64_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_Lsp_instHashableRefIdent_hash(v_x_178_);
lean_dec_ref(v_x_178_);
v_r_180_ = lean_box_uint64(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v_b_192_; lean_object* v_b_193_; 
if (lean_obj_tag(v_x_187_) == 0)
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_moduleName_196_; lean_object* v_identName_197_; lean_object* v_moduleName_198_; lean_object* v_identName_199_; 
v_moduleName_196_ = lean_ctor_get(v_x_187_, 0);
v_identName_197_ = lean_ctor_get(v_x_187_, 1);
v_moduleName_198_ = lean_ctor_get(v_x_188_, 0);
v_identName_199_ = lean_ctor_get(v_x_188_, 1);
v_a_190_ = v_moduleName_196_;
v_a_191_ = v_identName_197_;
v_b_192_ = v_moduleName_198_;
v_b_193_ = v_identName_199_;
goto v___jp_189_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
else
{
if (lean_obj_tag(v_x_188_) == 0)
{
uint8_t v___x_201_; 
v___x_201_ = 2;
return v___x_201_;
}
else
{
lean_object* v_moduleName_202_; lean_object* v_id_203_; lean_object* v_moduleName_204_; lean_object* v_id_205_; 
v_moduleName_202_ = lean_ctor_get(v_x_187_, 0);
v_id_203_ = lean_ctor_get(v_x_187_, 1);
v_moduleName_204_ = lean_ctor_get(v_x_188_, 0);
v_id_205_ = lean_ctor_get(v_x_188_, 1);
v_a_190_ = v_moduleName_202_;
v_a_191_ = v_id_203_;
v_b_192_ = v_moduleName_204_;
v_b_193_ = v_id_205_;
goto v___jp_189_;
}
}
v___jp_189_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_string_compare(v_a_190_, v_b_192_);
if (v___x_194_ == 1)
{
uint8_t v___x_195_; 
v___x_195_ = lean_string_compare(v_a_191_, v_b_193_);
if (v___x_195_ == 1)
{
return v___x_195_;
}
else
{
return v___x_195_;
}
}
else
{
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent_ord___boxed(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_Lsp_instOrdRefIdent_ord(v_x_206_, v_x_207_);
lean_dec_ref(v_x_207_);
lean_dec_ref(v_x_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx(lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(0u);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(1u);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___boxed(lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx(v_x_215_);
lean_dec_ref(v_x_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(lean_object* v_t_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_m_219_; lean_object* v_n_220_; lean_object* v___x_221_; 
v_m_219_ = lean_ctor_get(v_t_217_, 0);
lean_inc_ref(v_m_219_);
v_n_220_ = lean_ctor_get(v_t_217_, 1);
lean_inc_ref(v_n_220_);
lean_dec_ref(v_t_217_);
v___x_221_ = lean_apply_2(v_k_218_, v_m_219_, v_n_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(lean_object* v_motive_222_, lean_object* v_ctorIdx_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_k_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_224_, v_k_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___boxed(lean_object* v_motive_228_, lean_object* v_ctorIdx_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_k_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(v_motive_228_, v_ctorIdx_229_, v_t_230_, v_h_231_, v_k_232_);
lean_dec(v_ctorIdx_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim___redArg(lean_object* v_t_234_, lean_object* v_c_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_234_, v_c_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_c_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_238_, v_c_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim___redArg(lean_object* v_t_242_, lean_object* v_f_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_242_, v_f_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim(lean_object* v_motive_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_f_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_246_, v_f_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(lean_object* v_json_283_){
_start:
{
lean_object* v___x_284_; 
lean_inc(v_json_283_);
v___x_284_ = l_Lean_Json_getTag_x3f(v_json_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; 
lean_dec(v_json_283_);
v___x_285_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1));
return v___x_285_;
}
else
{
lean_object* v_val_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_val_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_284_, 1);
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_289_ = lean_string_dec_eq(v_val_286_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_291_ = lean_string_dec_eq(v_val_286_, v___x_290_);
lean_dec(v_val_286_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec(v_json_283_);
v___x_292_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5));
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11));
v___x_295_ = l_Lean_Json_parseCtorFields(v_json_283_, v___x_290_, v___x_293_, v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_304_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_295_, 1);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_array_get_borrowed(v___x_287_, v_a_304_, v___x_305_);
lean_inc(v___x_306_);
v___x_307_ = l_Lean_Json_getStr_x3f(v___x_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_a_304_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_a_316_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_307_, 1);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_array_get(v___x_287_, v_a_304_, v___x_317_);
lean_dec(v_a_304_);
v___x_319_ = l_Lean_Json_getStr_x3f(v___x_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec(v_a_316_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_a_328_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v___x_319_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_a_316_);
lean_ctor_set(v___x_332_, 1, v_a_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_val_286_);
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15));
v___x_339_ = l_Lean_Json_parseCtorFields(v_json_283_, v___x_288_, v___x_337_, v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_348_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_339_, 1);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_array_get_borrowed(v___x_287_, v_a_348_, v___x_349_);
lean_inc(v___x_350_);
v___x_351_ = l_Lean_Json_getStr_x3f(v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_348_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_351_, 1);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_array_get(v___x_287_, v_a_348_, v___x_361_);
lean_dec(v_a_348_);
v___x_363_ = l_Lean_Json_getStr_x3f(v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_a_360_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
v_a_372_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_380_ == 0)
{
v___x_374_ = v___x_363_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_363_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v_a_360_);
lean_ctor_set(v___x_376_, 1, v_a_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_376_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v_m_384_; lean_object* v_n_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_405_; 
v_m_384_ = lean_ctor_get(v_x_383_, 0);
v_n_385_ = lean_ctor_get(v_x_383_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_405_ == 0)
{
v___x_387_ = v_x_383_;
v_isShared_388_ = v_isSharedCheck_405_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_n_385_);
lean_inc(v_m_384_);
lean_dec(v_x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_405_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_389_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_390_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_391_, 0, v_m_384_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v___x_391_);
lean_ctor_set(v___x_387_, 0, v___x_390_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_391_);
v___x_393_ = v_reuseFailAlloc_404_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_394_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8));
v___x_395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_395_, 0, v_n_385_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_393_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = l_Lean_Json_mkObj(v___x_399_);
lean_dec_ref_known(v___x_399_, 2);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_389_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_397_);
v___x_403_ = l_Lean_Json_mkObj(v___x_402_);
lean_dec_ref_known(v___x_402_, 2);
return v___x_403_;
}
}
}
else
{
lean_object* v_m_406_; lean_object* v_i_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_427_; 
v_m_406_ = lean_ctor_get(v_x_383_, 0);
v_i_407_ = lean_ctor_get(v_x_383_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_383_);
if (v_isSharedCheck_427_ == 0)
{
v___x_409_ = v_x_383_;
v_isShared_410_ = v_isSharedCheck_427_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_i_407_);
lean_inc(v_m_406_);
lean_dec(v_x_383_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_427_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_411_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_412_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_413_, 0, v_m_406_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
lean_ctor_set(v___x_409_, 1, v___x_413_);
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_426_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_416_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12));
v___x_417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_417_, 0, v_i_407_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_415_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = l_Lean_Json_mkObj(v___x_421_);
lean_dec_ref_known(v___x_421_, 2);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_411_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_419_);
v___x_425_ = l_Lean_Json_mkObj(v___x_424_);
lean_dec_ref_known(v___x_424_, 2);
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_moduleName_431_; lean_object* v_identName_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_moduleName_431_ = lean_ctor_get(v_x_430_, 0);
v_identName_432_ = lean_ctor_get(v_x_430_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_x_430_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_identName_432_);
lean_inc(v_moduleName_431_);
lean_dec(v_x_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_moduleName_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_identName_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_moduleName_440_; lean_object* v_id_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_moduleName_440_ = lean_ctor_get(v_x_430_, 0);
v_id_441_ = lean_ctor_get(v_x_430_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v_x_430_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_id_441_);
lean_inc(v_moduleName_440_);
lean_dec(v_x_430_);
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
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_moduleName_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_id_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
lean_object* v_m_450_; lean_object* v_n_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_m_450_ = lean_ctor_get(v_x_449_, 0);
v_n_451_ = lean_ctor_get(v_x_449_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v_x_449_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_n_451_);
lean_inc(v_m_450_);
lean_dec(v_x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_m_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_n_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_m_459_; lean_object* v_i_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_m_459_ = lean_ctor_get(v_x_449_, 0);
v_i_460_ = lean_ctor_get(v_x_449_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v_x_449_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_i_460_);
lean_inc(v_m_459_);
lean_dec(v_x_449_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_m_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_i_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* v_s_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(v_s_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_a_478_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_486_ == 0)
{
v___x_480_ = v___x_469_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_469_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = l_Lean_Lsp_RefIdent_fromJsonRepr(v_a_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* v_id_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = l_Lean_Lsp_RefIdent_toJsonRepr(v_id_487_);
v___x_489_ = l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object* v_r_494_){
_start:
{
lean_object* v_range_495_; lean_object* v_pos_496_; lean_object* v_endPos_497_; lean_object* v_selectionRange_498_; lean_object* v_pos_499_; lean_object* v_endPos_500_; lean_object* v_charUtf16_501_; lean_object* v_endCharUtf16_502_; lean_object* v_line_503_; lean_object* v_line_504_; lean_object* v_charUtf16_505_; lean_object* v_endCharUtf16_506_; lean_object* v_line_507_; lean_object* v_line_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_range_495_ = lean_ctor_get(v_r_494_, 0);
v_pos_496_ = lean_ctor_get(v_range_495_, 0);
v_endPos_497_ = lean_ctor_get(v_range_495_, 2);
v_selectionRange_498_ = lean_ctor_get(v_r_494_, 1);
v_pos_499_ = lean_ctor_get(v_selectionRange_498_, 0);
v_endPos_500_ = lean_ctor_get(v_selectionRange_498_, 2);
v_charUtf16_501_ = lean_ctor_get(v_range_495_, 1);
v_endCharUtf16_502_ = lean_ctor_get(v_range_495_, 3);
v_line_503_ = lean_ctor_get(v_pos_496_, 0);
v_line_504_ = lean_ctor_get(v_endPos_497_, 0);
v_charUtf16_505_ = lean_ctor_get(v_selectionRange_498_, 1);
v_endCharUtf16_506_ = lean_ctor_get(v_selectionRange_498_, 3);
v_line_507_ = lean_ctor_get(v_pos_499_, 0);
v_line_508_ = lean_ctor_get(v_endPos_500_, 0);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_sub(v_line_503_, v___x_509_);
v___x_511_ = lean_nat_sub(v_line_504_, v___x_509_);
v___x_512_ = lean_nat_sub(v_line_507_, v___x_509_);
v___x_513_ = lean_nat_sub(v_line_508_, v___x_509_);
lean_inc(v_endCharUtf16_506_);
lean_inc(v_charUtf16_505_);
lean_inc(v_endCharUtf16_502_);
lean_inc(v_charUtf16_501_);
v___x_514_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_514_, 0, v___x_510_);
lean_ctor_set(v___x_514_, 1, v_charUtf16_501_);
lean_ctor_set(v___x_514_, 2, v___x_511_);
lean_ctor_set(v___x_514_, 3, v_endCharUtf16_502_);
lean_ctor_set(v___x_514_, 4, v___x_512_);
lean_ctor_set(v___x_514_, 5, v_charUtf16_505_);
lean_ctor_set(v___x_514_, 6, v___x_513_);
lean_ctor_set(v___x_514_, 7, v_endCharUtf16_506_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object* v_r_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_r_515_);
lean_dec_ref(v_r_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object* v_i_517_){
_start:
{
lean_object* v_rangeStartPosLine_518_; lean_object* v_rangeStartPosCharacter_519_; lean_object* v_rangeEndPosLine_520_; lean_object* v_rangeEndPosCharacter_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_rangeStartPosLine_518_ = lean_ctor_get(v_i_517_, 0);
v_rangeStartPosCharacter_519_ = lean_ctor_get(v_i_517_, 1);
v_rangeEndPosLine_520_ = lean_ctor_get(v_i_517_, 2);
v_rangeEndPosCharacter_521_ = lean_ctor_get(v_i_517_, 3);
lean_inc(v_rangeStartPosCharacter_519_);
lean_inc(v_rangeStartPosLine_518_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_rangeStartPosLine_518_);
lean_ctor_set(v___x_522_, 1, v_rangeStartPosCharacter_519_);
lean_inc(v_rangeEndPosCharacter_521_);
lean_inc(v_rangeEndPosLine_520_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_rangeEndPosLine_520_);
lean_ctor_set(v___x_523_, 1, v_rangeEndPosCharacter_521_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object* v_i_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Lsp_DeclInfo_range(v_i_525_);
lean_dec_ref(v_i_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object* v_i_527_){
_start:
{
lean_object* v_selectionRangeStartPosLine_528_; lean_object* v_selectionRangeStartPosCharacter_529_; lean_object* v_selectionRangeEndPosLine_530_; lean_object* v_selectionRangeEndPosCharacter_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_selectionRangeStartPosLine_528_ = lean_ctor_get(v_i_527_, 4);
v_selectionRangeStartPosCharacter_529_ = lean_ctor_get(v_i_527_, 5);
v_selectionRangeEndPosLine_530_ = lean_ctor_get(v_i_527_, 6);
v_selectionRangeEndPosCharacter_531_ = lean_ctor_get(v_i_527_, 7);
lean_inc(v_selectionRangeStartPosCharacter_529_);
lean_inc(v_selectionRangeStartPosLine_528_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_selectionRangeStartPosLine_528_);
lean_ctor_set(v___x_532_, 1, v_selectionRangeStartPosCharacter_529_);
lean_inc(v_selectionRangeEndPosCharacter_531_);
lean_inc(v_selectionRangeEndPosLine_530_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_selectionRangeEndPosLine_530_);
lean_ctor_set(v___x_533_, 1, v_selectionRangeEndPosCharacter_531_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object* v_i_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Lsp_DeclInfo_selectionRange(v_i_535_);
lean_dec_ref(v_i_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object* v_i_537_){
_start:
{
lean_object* v_rangeStartPosLine_538_; lean_object* v_rangeStartPosCharacter_539_; lean_object* v_rangeEndPosLine_540_; lean_object* v_rangeEndPosCharacter_541_; lean_object* v_selectionRangeStartPosLine_542_; lean_object* v_selectionRangeStartPosCharacter_543_; lean_object* v_selectionRangeEndPosLine_544_; lean_object* v_selectionRangeEndPosCharacter_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_rangeStartPosLine_538_ = lean_ctor_get(v_i_537_, 0);
lean_inc(v_rangeStartPosLine_538_);
v_rangeStartPosCharacter_539_ = lean_ctor_get(v_i_537_, 1);
lean_inc(v_rangeStartPosCharacter_539_);
v_rangeEndPosLine_540_ = lean_ctor_get(v_i_537_, 2);
lean_inc(v_rangeEndPosLine_540_);
v_rangeEndPosCharacter_541_ = lean_ctor_get(v_i_537_, 3);
lean_inc(v_rangeEndPosCharacter_541_);
v_selectionRangeStartPosLine_542_ = lean_ctor_get(v_i_537_, 4);
lean_inc(v_selectionRangeStartPosLine_542_);
v_selectionRangeStartPosCharacter_543_ = lean_ctor_get(v_i_537_, 5);
lean_inc(v_selectionRangeStartPosCharacter_543_);
v_selectionRangeEndPosLine_544_ = lean_ctor_get(v_i_537_, 6);
lean_inc(v_selectionRangeEndPosLine_544_);
v_selectionRangeEndPosCharacter_545_ = lean_ctor_get(v_i_537_, 7);
lean_inc(v_selectionRangeEndPosCharacter_545_);
lean_dec_ref(v_i_537_);
v___x_546_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_538_);
v___x_547_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_539_);
v___x_549_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
v___x_550_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_540_);
v___x_551_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_541_);
v___x_553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_542_);
v___x_555_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_543_);
v___x_557_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_544_);
v___x_559_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_545_);
v___x_561_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(8u);
v___x_563_ = lean_mk_empty_array_with_capacity(v___x_562_);
v___x_564_ = lean_array_push(v___x_563_, v___x_547_);
v___x_565_ = lean_array_push(v___x_564_, v___x_549_);
v___x_566_ = lean_array_push(v___x_565_, v___x_551_);
v___x_567_ = lean_array_push(v___x_566_, v___x_553_);
v___x_568_ = lean_array_push(v___x_567_, v___x_555_);
v___x_569_ = lean_array_push(v___x_568_, v___x_557_);
v___x_570_ = lean_array_push(v___x_569_, v___x_559_);
v___x_571_ = lean_array_push(v___x_570_, v___x_561_);
v___x_572_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object* v___x_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 4)
{
lean_object* v_elems_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_698_; 
v_elems_581_ = lean_ctor_get(v_x_580_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_698_ == 0)
{
v___x_583_ = v_x_580_;
v_isShared_584_ = v_isSharedCheck_698_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_elems_581_);
lean_dec(v_x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_698_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_array_get_size(v_elems_581_);
v___x_586_ = lean_unsigned_to_nat(8u);
v___x_587_ = lean_nat_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec_ref(v_elems_581_);
v___x_588_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_589_ = l_Nat_reprFast(v___x_585_);
v___x_590_ = lean_string_append(v___x_588_, v___x_589_);
lean_dec_ref(v___x_589_);
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
lean_ctor_set(v___x_583_, 0, v___x_590_);
v___x_592_ = v___x_583_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_583_);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_594_);
lean_inc(v___x_595_);
v___x_596_ = l_Lean_Json_getNat_x3f(v___x_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_elems_581_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_596_, 1);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_606_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Json_getNat_x3f(v___x_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_608_, 1);
v___x_618_ = lean_unsigned_to_nat(2u);
v___x_619_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_618_);
lean_inc(v___x_619_);
v___x_620_ = l_Lean_Json_getNat_x3f(v___x_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_617_);
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_a_629_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_620_, 1);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_630_);
lean_inc(v___x_631_);
v___x_632_ = l_Lean_Json_getNat_x3f(v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_629_);
lean_dec(v_a_617_);
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_632_, 1);
v___x_642_ = lean_unsigned_to_nat(4u);
v___x_643_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_642_);
lean_inc(v___x_643_);
v___x_644_ = l_Lean_Json_getNat_x3f(v___x_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_a_641_);
lean_dec(v_a_629_);
lean_dec(v_a_617_);
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_653_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_644_, 1);
v___x_654_ = lean_unsigned_to_nat(5u);
v___x_655_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_654_);
lean_inc(v___x_655_);
v___x_656_ = l_Lean_Json_getNat_x3f(v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_a_653_);
lean_dec(v_a_641_);
lean_dec(v_a_629_);
lean_dec(v_a_617_);
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_665_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_656_, 1);
v___x_666_ = lean_unsigned_to_nat(6u);
v___x_667_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_666_);
lean_inc(v___x_667_);
v___x_668_ = l_Lean_Json_getNat_x3f(v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_665_);
lean_dec(v_a_653_);
lean_dec(v_a_641_);
lean_dec(v_a_629_);
lean_dec(v_a_617_);
lean_dec(v_a_605_);
lean_dec_ref(v_elems_581_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_a_677_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_668_, 1);
v___x_678_ = lean_unsigned_to_nat(7u);
v___x_679_ = lean_array_get(v___x_579_, v_elems_581_, v___x_678_);
lean_dec_ref(v_elems_581_);
v___x_680_ = l_Lean_Json_getNat_x3f(v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec(v_a_677_);
lean_dec(v_a_665_);
lean_dec(v_a_653_);
lean_dec(v_a_641_);
lean_dec(v_a_629_);
lean_dec(v_a_617_);
lean_dec(v_a_605_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_a_689_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_697_ == 0)
{
v___x_691_ = v___x_680_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_680_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_693_, 0, v_a_605_);
lean_ctor_set(v___x_693_, 1, v_a_617_);
lean_ctor_set(v___x_693_, 2, v_a_629_);
lean_ctor_set(v___x_693_, 3, v_a_641_);
lean_ctor_set(v___x_693_, 4, v_a_653_);
lean_ctor_set(v___x_693_, 5, v_a_665_);
lean_ctor_set(v___x_693_, 6, v_a_677_);
lean_ctor_set(v___x_693_, 7, v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
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
lean_object* v___x_699_; 
lean_dec(v_x_580_);
v___x_699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object* v___x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Lsp_instFromJsonDeclInfo___lam__0(v___x_700_, v_x_701_);
lean_dec(v___x_700_);
return v_res_702_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(1);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(1);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_c_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_709_);
lean_ctor_set(v___x_712_, 1, v_b_710_);
v___x_713_ = lean_apply_2(v_f_708_, v___x_712_, v_c_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_733_, lean_object* v_init_734_, lean_object* v_f_735_){
_start:
{
lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_a_739_; 
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_736_, 0, v_f_735_);
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_738_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_737_, v___f_736_, v_init_734_, v_m_733_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec(v___x_738_);
return v_a_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_740_, lean_object* v_m_741_, lean_object* v_init_742_, lean_object* v_f_743_){
_start:
{
lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_a_747_; 
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_744_, 0, v_f_743_);
v___x_745_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_746_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_745_, v___f_744_, v_init_742_, v_m_741_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec(v___x_746_);
return v_a_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_748_, lean_object* v_init_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_l_753_; lean_object* v_r_754_; lean_object* v___x_755_; 
v_k_751_ = lean_ctor_get(v_x_750_, 1);
v_v_752_ = lean_ctor_get(v_x_750_, 2);
v_l_753_ = lean_ctor_get(v_x_750_, 3);
v_r_754_ = lean_ctor_get(v_x_750_, 4);
lean_inc_ref(v___y_748_);
v___x_755_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_748_, v_init_749_, v_l_753_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref(v___y_748_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
lean_inc(v_v_752_);
lean_inc(v_k_751_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_k_751_);
lean_ctor_set(v___x_757_, 1, v_v_752_);
lean_inc_ref(v___y_748_);
v___x_758_ = lean_apply_2(v___y_748_, v___x_757_, v_a_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref(v___y_748_);
return v___x_758_;
}
else
{
lean_object* v_a_759_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v_init_749_ = v_a_759_;
v_x_750_ = v_r_754_;
goto _start;
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v___y_748_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_init_749_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_762_, lean_object* v_init_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_762_, v_init_763_, v_x_764_);
lean_dec(v_x_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_770_; lean_object* v_a_771_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_769_, v___y_768_, v___y_767_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
return v_a_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v_init_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_780_, v_init_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v_init_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_784_, v___y_785_, v_init_786_, v_x_787_);
lean_dec(v_x_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_789_){
_start:
{
lean_object* v_snd_790_; lean_object* v_fst_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_833_; 
v_snd_790_ = lean_ctor_get(v_x_789_, 1);
v_fst_791_ = lean_ctor_get(v_x_789_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_789_);
if (v_isSharedCheck_833_ == 0)
{
v___x_793_ = v_x_789_;
v_isShared_794_ = v_isSharedCheck_833_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_791_);
lean_dec(v_x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_833_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_rangeStartPosLine_795_; lean_object* v_rangeStartPosCharacter_796_; lean_object* v_rangeEndPosLine_797_; lean_object* v_rangeEndPosCharacter_798_; lean_object* v_selectionRangeStartPosLine_799_; lean_object* v_selectionRangeStartPosCharacter_800_; lean_object* v_selectionRangeEndPosLine_801_; lean_object* v_selectionRangeEndPosCharacter_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v_rangeStartPosLine_795_ = lean_ctor_get(v_snd_790_, 0);
lean_inc(v_rangeStartPosLine_795_);
v_rangeStartPosCharacter_796_ = lean_ctor_get(v_snd_790_, 1);
lean_inc(v_rangeStartPosCharacter_796_);
v_rangeEndPosLine_797_ = lean_ctor_get(v_snd_790_, 2);
lean_inc(v_rangeEndPosLine_797_);
v_rangeEndPosCharacter_798_ = lean_ctor_get(v_snd_790_, 3);
lean_inc(v_rangeEndPosCharacter_798_);
v_selectionRangeStartPosLine_799_ = lean_ctor_get(v_snd_790_, 4);
lean_inc(v_selectionRangeStartPosLine_799_);
v_selectionRangeStartPosCharacter_800_ = lean_ctor_get(v_snd_790_, 5);
lean_inc(v_selectionRangeStartPosCharacter_800_);
v_selectionRangeEndPosLine_801_ = lean_ctor_get(v_snd_790_, 6);
lean_inc(v_selectionRangeEndPosLine_801_);
v_selectionRangeEndPosCharacter_802_ = lean_ctor_get(v_snd_790_, 7);
lean_inc(v_selectionRangeEndPosCharacter_802_);
lean_dec(v_snd_790_);
v___x_803_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_795_);
v___x_804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_796_);
v___x_806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_797_);
v___x_808_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_798_);
v___x_810_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_799_);
v___x_812_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_800_);
v___x_814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_801_);
v___x_816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_802_);
v___x_818_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_unsigned_to_nat(8u);
v___x_820_ = lean_mk_empty_array_with_capacity(v___x_819_);
v___x_821_ = lean_array_push(v___x_820_, v___x_804_);
v___x_822_ = lean_array_push(v___x_821_, v___x_806_);
v___x_823_ = lean_array_push(v___x_822_, v___x_808_);
v___x_824_ = lean_array_push(v___x_823_, v___x_810_);
v___x_825_ = lean_array_push(v___x_824_, v___x_812_);
v___x_826_ = lean_array_push(v___x_825_, v___x_814_);
v___x_827_ = lean_array_push(v___x_826_, v___x_816_);
v___x_828_ = lean_array_push(v___x_827_, v___x_818_);
v___x_829_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_829_);
v___x_831_ = v___x_793_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_fst_791_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_834_, lean_object* v_x2_835_, lean_object* v_x3_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_x1_834_);
lean_ctor_set(v___x_837_, 1, v_x2_835_);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_x3_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_839_, lean_object* v___f_840_, lean_object* v_m_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_842_ = lean_box(0);
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_844_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_843_, v___f_839_, v___x_842_, v_m_841_);
v___x_845_ = l_List_mapTR_loop___redArg(v___f_840_, v___x_844_, v___x_842_);
v___x_846_ = l_Lean_Json_mkObj(v___x_845_);
lean_dec(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v___x_855_, lean_object* v_m_856_, lean_object* v_k_857_, lean_object* v_v_858_){
_start:
{
if (lean_obj_tag(v_v_858_) == 4)
{
lean_object* v_elems_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_978_; 
v_elems_859_ = lean_ctor_get(v_v_858_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v_v_858_);
if (v_isSharedCheck_978_ == 0)
{
v___x_861_ = v_v_858_;
v_isShared_862_ = v_isSharedCheck_978_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_elems_859_);
lean_dec(v_v_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_978_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = lean_array_get_size(v_elems_859_);
v___x_864_ = lean_unsigned_to_nat(8u);
v___x_865_ = lean_nat_dec_eq(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v___x_866_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_867_ = l_Nat_reprFast(v___x_863_);
v___x_868_ = lean_string_append(v___x_866_, v___x_867_);
lean_dec_ref(v___x_867_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 0);
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_del_object(v___x_861_);
v___x_872_ = lean_box(0);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_873_);
lean_inc(v___x_874_);
v___x_875_ = l_Lean_Json_getNat_x3f(v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_884_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_875_, 1);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_885_);
lean_inc(v___x_886_);
v___x_887_ = l_Lean_Json_getNat_x3f(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_a_896_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_887_, 1);
v___x_897_ = lean_unsigned_to_nat(2u);
v___x_898_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_897_);
lean_inc(v___x_898_);
v___x_899_ = l_Lean_Json_getNat_x3f(v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_899_, 1);
v___x_909_ = lean_unsigned_to_nat(3u);
v___x_910_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_909_);
lean_inc(v___x_910_);
v___x_911_ = l_Lean_Json_getNat_x3f(v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_908_);
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_a_920_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_911_, 1);
v___x_921_ = lean_unsigned_to_nat(4u);
v___x_922_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_921_);
lean_inc(v___x_922_);
v___x_923_ = l_Lean_Json_getNat_x3f(v___x_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_920_);
lean_dec(v_a_908_);
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_932_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_923_, 1);
v___x_933_ = lean_unsigned_to_nat(5u);
v___x_934_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_933_);
lean_inc(v___x_934_);
v___x_935_ = l_Lean_Json_getNat_x3f(v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_a_932_);
lean_dec(v_a_920_);
lean_dec(v_a_908_);
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_a_944_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_935_, 1);
v___x_945_ = lean_unsigned_to_nat(6u);
v___x_946_ = lean_array_get_borrowed(v___x_872_, v_elems_859_, v___x_945_);
lean_inc(v___x_946_);
v___x_947_ = l_Lean_Json_getNat_x3f(v___x_946_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_a_944_);
lean_dec(v_a_932_);
lean_dec(v_a_920_);
lean_dec(v_a_908_);
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_elems_859_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_956_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_947_, 1);
v___x_957_ = lean_unsigned_to_nat(7u);
v___x_958_ = lean_array_get(v___x_872_, v_elems_859_, v___x_957_);
lean_dec_ref(v_elems_859_);
v___x_959_ = l_Lean_Json_getNat_x3f(v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_a_956_);
lean_dec(v_a_944_);
lean_dec(v_a_932_);
lean_dec(v_a_920_);
lean_dec(v_a_908_);
lean_dec(v_a_896_);
lean_dec(v_a_884_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_a_968_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v___x_959_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_959_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_972_, 0, v_a_884_);
lean_ctor_set(v___x_972_, 1, v_a_896_);
lean_ctor_set(v___x_972_, 2, v_a_908_);
lean_ctor_set(v___x_972_, 3, v_a_920_);
lean_ctor_set(v___x_972_, 4, v_a_932_);
lean_ctor_set(v___x_972_, 5, v_a_944_);
lean_ctor_set(v___x_972_, 6, v_a_956_);
lean_ctor_set(v___x_972_, 7, v_a_968_);
v___x_973_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_855_, v_k_857_, v___x_972_, v_m_856_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
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
lean_object* v___x_979_; 
lean_dec(v_v_858_);
lean_dec_ref(v_k_857_);
lean_dec(v_m_856_);
lean_dec_ref(v___x_855_);
v___x_979_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___x_983_, lean_object* v_j_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Json_getObj_x3f(v_j_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v___x_983_);
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_a_994_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_985_, 1);
v___f_995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1));
v___x_996_ = lean_box(1);
v___x_997_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_983_, v___f_995_, v___x_996_, v_a_994_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1025_, lean_object* v_parentDecl_x3f_1026_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1026_) == 0)
{
lean_object* v_start_1027_; lean_object* v_end_1028_; lean_object* v_line_1029_; lean_object* v_character_1030_; lean_object* v_line_1031_; lean_object* v_character_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_start_1027_ = lean_ctor_get(v_range_1025_, 0);
v_end_1028_ = lean_ctor_get(v_range_1025_, 1);
v_line_1029_ = lean_ctor_get(v_start_1027_, 0);
v_character_1030_ = lean_ctor_get(v_start_1027_, 1);
v_line_1031_ = lean_ctor_get(v_end_1028_, 0);
v_character_1032_ = lean_ctor_get(v_end_1028_, 1);
v___x_1033_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1032_);
lean_inc(v_line_1031_);
lean_inc(v_character_1030_);
lean_inc(v_line_1029_);
v___x_1034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1034_, 0, v_line_1029_);
lean_ctor_set(v___x_1034_, 1, v_character_1030_);
lean_ctor_set(v___x_1034_, 2, v_line_1031_);
lean_ctor_set(v___x_1034_, 3, v_character_1032_);
lean_ctor_set(v___x_1034_, 4, v___x_1033_);
return v___x_1034_;
}
else
{
lean_object* v_start_1035_; lean_object* v_end_1036_; lean_object* v_line_1037_; lean_object* v_character_1038_; lean_object* v_line_1039_; lean_object* v_character_1040_; lean_object* v_val_1041_; lean_object* v___x_1042_; 
v_start_1035_ = lean_ctor_get(v_range_1025_, 0);
v_end_1036_ = lean_ctor_get(v_range_1025_, 1);
v_line_1037_ = lean_ctor_get(v_start_1035_, 0);
v_character_1038_ = lean_ctor_get(v_start_1035_, 1);
v_line_1039_ = lean_ctor_get(v_end_1036_, 0);
v_character_1040_ = lean_ctor_get(v_end_1036_, 1);
v_val_1041_ = lean_ctor_get(v_parentDecl_x3f_1026_, 0);
lean_inc(v_val_1041_);
lean_inc(v_character_1040_);
lean_inc(v_line_1039_);
lean_inc(v_character_1038_);
lean_inc(v_line_1037_);
v___x_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1042_, 0, v_line_1037_);
lean_ctor_set(v___x_1042_, 1, v_character_1038_);
lean_ctor_set(v___x_1042_, 2, v_line_1039_);
lean_ctor_set(v___x_1042_, 3, v_character_1040_);
lean_ctor_set(v___x_1042_, 4, v_val_1041_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1043_, lean_object* v_parentDecl_x3f_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1043_, v_parentDecl_x3f_1044_);
lean_dec(v_parentDecl_x3f_1044_);
lean_dec_ref(v_range_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1046_){
_start:
{
lean_object* v_startPosLine_1047_; lean_object* v_startPosCharacter_1048_; lean_object* v_endPosLine_1049_; lean_object* v_endPosCharacter_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_startPosLine_1047_ = lean_ctor_get(v_l_1046_, 0);
v_startPosCharacter_1048_ = lean_ctor_get(v_l_1046_, 1);
v_endPosLine_1049_ = lean_ctor_get(v_l_1046_, 2);
v_endPosCharacter_1050_ = lean_ctor_get(v_l_1046_, 3);
lean_inc(v_startPosCharacter_1048_);
lean_inc(v_startPosLine_1047_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_startPosLine_1047_);
lean_ctor_set(v___x_1051_, 1, v_startPosCharacter_1048_);
lean_inc(v_endPosCharacter_1050_);
lean_inc(v_endPosLine_1049_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_endPosLine_1049_);
lean_ctor_set(v___x_1052_, 1, v_endPosCharacter_1050_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1054_);
lean_dec_ref(v_l_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1056_){
_start:
{
lean_object* v_parentDecl_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_parentDecl_1057_ = lean_ctor_get(v_l_1056_, 4);
v___x_1058_ = lean_string_utf8_byte_size(v_parentDecl_1057_);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_nat_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_inc_ref(v_parentDecl_1057_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_parentDecl_1057_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_box(0);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1063_);
lean_dec_ref(v_l_1063_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Lean_JsonNumber_fromNat(v_n_1065_);
v___x_1067_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1068_, lean_object* v_l_1069_){
_start:
{
lean_object* v_startPosLine_1070_; lean_object* v_startPosCharacter_1071_; lean_object* v_endPosLine_1072_; lean_object* v_endPosCharacter_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v_range_1079_; lean_object* v___x_1080_; 
v_startPosLine_1070_ = lean_ctor_get(v_l_1069_, 0);
v_startPosCharacter_1071_ = lean_ctor_get(v_l_1069_, 1);
v_endPosLine_1072_ = lean_ctor_get(v_l_1069_, 2);
v_endPosCharacter_1073_ = lean_ctor_get(v_l_1069_, 3);
v___x_1074_ = lean_box(0);
lean_inc(v_endPosCharacter_1073_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_endPosCharacter_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc(v_endPosLine_1072_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_endPosLine_1072_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
lean_inc(v_startPosCharacter_1071_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_startPosCharacter_1071_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_inc(v_startPosLine_1070_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_startPosLine_1070_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v_range_1079_ = l_List_mapTR_loop___redArg(v___f_1068_, v___x_1078_, v___x_1074_);
v___x_1080_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1069_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = l_List_appendTR___redArg(v_range_1079_, v___x_1074_);
return v___x_1081_;
}
else
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1091_; 
v_val_1082_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1084_ = v___x_1080_;
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v___x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1091_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 3);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_val_1082_);
v___x_1087_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1074_);
v___x_1089_ = l_List_appendTR___redArg(v_range_1079_, v___x_1088_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1092_, lean_object* v_l_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1092_, v_l_1093_);
lean_dec_ref(v_l_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1095_, lean_object* v_x_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_apply_1(v_locationToList_1095_, v_x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1100_, lean_object* v___f_1101_, lean_object* v_locationToList_1102_, lean_object* v_i_1103_){
_start:
{
lean_object* v_definition_x3f_1104_; lean_object* v_usages_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1137_; 
v_definition_x3f_1104_ = lean_ctor_get(v_i_1103_, 0);
v_usages_1105_ = lean_ctor_get(v_i_1103_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_i_1103_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1107_ = v_i_1103_;
v_isShared_1108_ = v_isSharedCheck_1137_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_usages_1105_);
lean_inc(v_definition_x3f_1104_);
lean_dec(v_i_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1137_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___y_1111_; 
v___x_1109_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1104_) == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v_locationToList_1102_);
v___x_1127_ = lean_box(0);
v___y_1111_ = v___x_1127_;
goto v___jp_1110_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v_val_1128_ = lean_ctor_get(v_definition_x3f_1104_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_definition_x3f_1104_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v_definition_x3f_1104_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v_definition_x3f_1104_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_apply_1(v_locationToList_1102_, v_val_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v___y_1111_ = v___x_1134_;
goto v___jp_1110_;
}
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
lean_inc_ref(v___x_1100_);
v___x_1112_ = l_Option_toJson___redArg(v___x_1100_, v___y_1111_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v___x_1112_);
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1114_ = v___x_1107_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1115_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1117_ = lean_array_size(v_usages_1105_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1116_, v___f_1101_, v_sz_1117_, v___x_1118_, v_usages_1105_);
v___x_1120_ = l_Array_toJson___redArg(v___x_1100_, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1115_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_box(0);
v___x_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1114_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_Json_mkObj(v___x_1124_);
lean_dec_ref_known(v___x_1124_, 2);
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1234_; 
v___x_1153_ = lean_array_get_size(v_a_1152_);
v___x_1154_ = lean_unsigned_to_nat(4u);
v___x_1234_ = lean_nat_dec_eq(v___x_1153_, v___x_1154_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(5u);
v___x_1236_ = lean_nat_dec_eq(v___x_1153_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1238_ = l_Nat_reprFast(v___x_1153_);
v___x_1239_ = lean_string_append(v___x_1237_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
else
{
goto v___jp_1155_;
}
}
else
{
goto v___jp_1155_;
}
v___jp_1155_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_fget_borrowed(v_a_1152_, v___x_1156_);
lean_inc(v___x_1157_);
v___x_1158_ = l_Lean_Json_getNat_x3f(v___x_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
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
v___x_1168_ = lean_unsigned_to_nat(1u);
v___x_1169_ = lean_array_fget_borrowed(v_a_1152_, v___x_1168_);
lean_inc(v___x_1169_);
v___x_1170_ = l_Lean_Json_getNat_x3f(v___x_1169_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v_a_1167_);
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
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = lean_array_fget_borrowed(v_a_1152_, v___x_1180_);
lean_inc(v___x_1181_);
v___x_1182_ = l_Lean_Json_getNat_x3f(v___x_1181_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
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
v___x_1192_ = lean_unsigned_to_nat(3u);
v___x_1193_ = lean_array_fget_borrowed(v_a_1152_, v___x_1192_);
lean_inc(v___x_1193_);
v___x_1194_ = l_Lean_Json_getNat_x3f(v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_a_1191_);
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
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
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1233_; 
v_a_1203_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1205_ = v___x_1194_;
v_isShared_1206_ = v_isSharedCheck_1233_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1194_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1233_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_unsigned_to_nat(5u);
v___x_1208_ = lean_nat_dec_eq(v___x_1153_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1210_, 0, v_a_1167_);
lean_ctor_set(v___x_1210_, 1, v_a_1179_);
lean_ctor_set(v___x_1210_, 2, v_a_1191_);
lean_ctor_set(v___x_1210_, 3, v_a_1203_);
lean_ctor_set(v___x_1210_, 4, v___x_1209_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1210_);
v___x_1212_ = v___x_1205_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_del_object(v___x_1205_);
v___x_1214_ = lean_array_fget_borrowed(v_a_1152_, v___x_1154_);
lean_inc(v___x_1214_);
v___x_1215_ = l_Lean_Json_getStr_x3f(v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1203_);
lean_dec(v_a_1191_);
lean_dec(v_a_1179_);
lean_dec(v_a_1167_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1232_; 
v_a_1224_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1226_ = v___x_1215_;
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1215_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1232_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1167_);
lean_ctor_set(v___x_1228_, 1, v_a_1179_);
lean_ctor_set(v___x_1228_, 2, v_a_1191_);
lean_ctor_set(v___x_1228_, 3, v_a_1203_);
lean_ctor_set(v___x_1228_, 4, v_a_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1241_);
lean_dec_ref(v_a_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v_toLocation_1246_, lean_object* v_j_1247_){
_start:
{
lean_object* v_definition_x3f_1249_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1247_);
v___x_1282_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1247_, v___x_1243_, v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_j_1247_);
lean_dec_ref(v_toLocation_1246_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1244_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1282_, 1);
if (lean_obj_tag(v_a_1291_) == 0)
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_box(0);
v_definition_x3f_1249_ = v___x_1292_;
goto v___jp_1248_;
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1310_; 
v_val_1293_ = lean_ctor_get(v_a_1291_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1291_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1295_ = v_a_1291_;
v_isShared_1296_ = v_isSharedCheck_1310_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_val_1293_);
lean_dec(v_a_1291_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1310_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; 
lean_inc_ref(v_toLocation_1246_);
v___x_1297_ = lean_apply_1(v_toLocation_1246_, v_val_1293_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_del_object(v___x_1295_);
lean_dec(v_j_1247_);
lean_dec_ref(v_toLocation_1246_);
lean_dec_ref(v___x_1245_);
lean_dec_ref(v___x_1244_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; 
v_a_1306_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1297_, 1);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_a_1306_);
v___x_1308_ = v___x_1295_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_definition_x3f_1249_ = v___x_1308_;
goto v___jp_1248_;
}
}
}
}
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1251_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1247_, v___x_1244_, v___x_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v_definition_x3f_1249_);
lean_dec_ref(v_toLocation_1246_);
lean_dec_ref(v___x_1245_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v_a_1260_; size_t v_sz_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1260_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1251_, 1);
v_sz_1261_ = lean_array_size(v_a_1260_);
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1245_, v_toLocation_1246_, v_sz_1261_, v___x_1262_, v_a_1260_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_definition_x3f_1249_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1263_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1263_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_definition_x3f_1249_);
lean_ctor_set(v___x_1276_, 1, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
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
lean_object* v___x_1325_; 
v___x_1325_ = lean_box(1);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_box(1);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1327_, lean_object* v_a_1328_, lean_object* v_b_1329_, lean_object* v_c_1330_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1328_);
lean_ctor_set(v___x_1331_, 1, v_b_1329_);
v___x_1332_ = lean_apply_2(v_f_1327_, v___x_1331_, v_c_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1333_, lean_object* v_____do__lift_1334_){
_start:
{
lean_object* v_a_1335_; lean_object* v___x_1336_; 
v_a_1335_ = lean_ctor_get(v_____do__lift_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref(v_____do__lift_1334_);
v___x_1336_ = lean_apply_2(v_toPure_1333_, lean_box(0), v_a_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_map_1339_, lean_object* v_init_1340_, lean_object* v_f_1341_){
_start:
{
lean_object* v_toApplicative_1342_; lean_object* v_toBind_1343_; lean_object* v_toPure_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v_toApplicative_1342_ = lean_ctor_get(v_inst_1337_, 0);
v_toBind_1343_ = lean_ctor_get(v_inst_1337_, 1);
lean_inc(v_toBind_1343_);
v_toPure_1344_ = lean_ctor_get(v_toApplicative_1342_, 1);
lean_inc(v_toPure_1344_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1345_, 0, v_f_1341_);
v___x_1346_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1337_, v___f_1345_, v_init_1340_, v_map_1339_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1347_, 0, v_toPure_1344_);
v___x_1348_ = lean_apply_4(v_toBind_1343_, lean_box(0), lean_box(0), v___x_1346_, v___f_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1349_){
_start:
{
lean_object* v___f_1350_; 
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1350_, 0, v_inst_1349_);
return v___f_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1351_, lean_object* v_inst_1352_){
_start:
{
lean_object* v___f_1353_; 
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1353_, 0, v_inst_1352_);
return v___f_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v_startPosLine_1356_; lean_object* v_startPosCharacter_1357_; lean_object* v_endPosLine_1358_; lean_object* v_endPosCharacter_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_range_1365_; lean_object* v___x_1366_; 
v_startPosLine_1356_ = lean_ctor_get(v_x_1355_, 0);
v_startPosCharacter_1357_ = lean_ctor_get(v_x_1355_, 1);
v_endPosLine_1358_ = lean_ctor_get(v_x_1355_, 2);
v_endPosCharacter_1359_ = lean_ctor_get(v_x_1355_, 3);
v___x_1360_ = lean_box(0);
lean_inc(v_endPosCharacter_1359_);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_endPosCharacter_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_inc(v_endPosLine_1358_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_endPosLine_1358_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc(v_startPosCharacter_1357_);
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_startPosCharacter_1357_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
lean_inc(v_startPosLine_1356_);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_startPosLine_1356_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v_range_1365_ = l_List_mapTR_loop___redArg(v___f_1354_, v___x_1364_, v___x_1360_);
v___x_1366_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1355_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = l_List_appendTR___redArg(v_range_1365_, v___x_1360_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_val_1368_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 3);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_val_1368_);
v___x_1373_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v___x_1360_);
v___x_1375_ = l_List_appendTR___redArg(v_range_1365_, v___x_1374_);
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1378_, v_x_1379_);
lean_dec_ref(v_x_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1381_, lean_object* v___f_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v_snd_1384_; lean_object* v_fst_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1446_; 
v_snd_1384_ = lean_ctor_get(v_x_1383_, 1);
v_fst_1385_ = lean_ctor_get(v_x_1383_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1383_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1387_ = v_x_1383_;
v_isShared_1388_ = v_isSharedCheck_1446_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1385_);
lean_dec(v_x_1383_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1446_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_definition_x3f_1389_; lean_object* v_usages_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1445_; 
v_definition_x3f_1389_ = lean_ctor_get(v_snd_1384_, 0);
v_usages_1390_ = lean_ctor_get(v_snd_1384_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_snd_1384_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1392_ = v_snd_1384_;
v_isShared_1393_ = v_isSharedCheck_1445_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_usages_1390_);
lean_inc(v_definition_x3f_1389_);
lean_dec(v_snd_1384_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1445_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___y_1419_; 
v___x_1394_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1385_);
v___x_1395_ = l_Lean_Json_compress(v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1397_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1389_) == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v___f_1382_);
v___x_1421_ = lean_box(0);
v___y_1399_ = v___x_1421_;
goto v___jp_1398_;
}
else
{
lean_object* v_val_1422_; lean_object* v_startPosLine_1423_; lean_object* v_startPosCharacter_1424_; lean_object* v_endPosLine_1425_; lean_object* v_endPosCharacter_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_range_1432_; lean_object* v___x_1433_; 
v_val_1422_ = lean_ctor_get(v_definition_x3f_1389_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v_definition_x3f_1389_, 1);
v_startPosLine_1423_ = lean_ctor_get(v_val_1422_, 0);
v_startPosCharacter_1424_ = lean_ctor_get(v_val_1422_, 1);
v_endPosLine_1425_ = lean_ctor_get(v_val_1422_, 2);
v_endPosCharacter_1426_ = lean_ctor_get(v_val_1422_, 3);
v___x_1427_ = lean_box(0);
lean_inc(v_endPosCharacter_1426_);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_endPosCharacter_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
lean_inc(v_endPosLine_1425_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_endPosLine_1425_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc(v_startPosCharacter_1424_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_startPosCharacter_1424_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc(v_startPosLine_1423_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_startPosLine_1423_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v_range_1432_ = l_List_mapTR_loop___redArg(v___f_1382_, v___x_1431_, v___x_1427_);
v___x_1433_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1422_);
lean_dec(v_val_1422_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = l_List_appendTR___redArg(v_range_1432_, v___x_1427_);
v___y_1419_ = v___x_1434_;
goto v___jp_1418_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1444_; 
v_val_1435_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1437_ = v___x_1433_;
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_val_1435_);
lean_dec(v___x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1444_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 3);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_val_1435_);
v___x_1440_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1427_);
v___x_1442_ = l_List_appendTR___redArg(v_range_1432_, v___x_1441_);
v___y_1419_ = v___x_1442_;
goto v___jp_1418_;
}
}
}
}
v___jp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Option_toJson___redArg(v___x_1396_, v___y_1399_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1400_);
lean_ctor_set(v___x_1387_, 0, v___x_1397_);
v___x_1402_ = v___x_1387_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; size_t v_sz_1405_; size_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1403_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1404_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1405_ = lean_array_size(v_usages_1390_);
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1404_, v___f_1381_, v_sz_1405_, v___x_1406_, v_usages_1390_);
v___x_1408_ = l_Array_toJson___redArg(v___x_1396_, v___x_1407_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___x_1408_);
lean_ctor_set(v___x_1392_, 0, v___x_1403_);
v___x_1410_ = v___x_1392_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1402_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_Json_mkObj(v___x_1413_);
lean_dec_ref_known(v___x_1413_, 2);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1395_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
return v___x_1415_;
}
}
}
v___jp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___y_1419_);
v___y_1399_ = v___x_1420_;
goto v___jp_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1447_, lean_object* v_x2_1448_, lean_object* v_x3_1449_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_x1_1447_);
lean_ctor_set(v___x_1450_, 1, v_x2_1448_);
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v_x3_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1452_, lean_object* v___f_1453_, lean_object* v_m_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1455_ = lean_box(0);
v___x_1456_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1456_, v___f_1452_, v___x_1455_, v_m_1454_);
v___x_1458_ = l_List_mapTR_loop___redArg(v___f_1453_, v___x_1457_, v___x_1455_);
v___x_1459_ = l_Lean_Json_mkObj(v___x_1458_);
lean_dec(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1470_, lean_object* v_m_1471_, lean_object* v_k_1472_, lean_object* v_v_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Json_parse(v_k_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1484_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_a_1493_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1494_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1495_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1496_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1473_);
v___x_1497_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1473_, v___x_1495_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1627_; 
v_a_1506_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1508_ = v___x_1497_;
v_isShared_1509_ = v_isSharedCheck_1627_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1497_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1627_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v_definition_x3f_1512_; lean_object* v_a_1547_; 
v___x_1510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1506_) == 0)
{
lean_object* v___x_1549_; 
lean_del_object(v___x_1508_);
v___x_1549_ = lean_box(0);
v_definition_x3f_1512_ = v___x_1549_;
goto v___jp_1511_;
}
else
{
lean_object* v_val_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1618_; 
v_val_1550_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v_a_1506_, 1);
v___x_1551_ = lean_array_get_size(v_val_1550_);
v___x_1552_ = lean_unsigned_to_nat(4u);
v___x_1618_ = lean_nat_dec_eq(v___x_1551_, v___x_1552_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = lean_unsigned_to_nat(5u);
v___x_1620_ = lean_nat_dec_eq(v___x_1551_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_val_1550_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v___x_1621_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1622_ = l_Nat_reprFast(v___x_1551_);
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
lean_dec_ref(v___x_1622_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1623_);
v___x_1625_ = v___x_1508_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_del_object(v___x_1508_);
goto v___jp_1553_;
}
}
else
{
lean_del_object(v___x_1508_);
goto v___jp_1553_;
}
v___jp_1553_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_unsigned_to_nat(0u);
v___x_1555_ = lean_array_fget_borrowed(v_val_1550_, v___x_1554_);
lean_inc(v___x_1555_);
v___x_1556_ = l_Lean_Json_getNat_x3f(v___x_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_val_1550_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
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
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_array_fget_borrowed(v_val_1550_, v___x_1566_);
lean_inc(v___x_1567_);
v___x_1568_ = l_Lean_Json_getNat_x3f(v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1565_);
lean_dec(v_val_1550_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
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
v___x_1578_ = lean_unsigned_to_nat(2u);
v___x_1579_ = lean_array_fget_borrowed(v_val_1550_, v___x_1578_);
lean_inc(v___x_1579_);
v___x_1580_ = l_Lean_Json_getNat_x3f(v___x_1579_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1577_);
lean_dec(v_a_1565_);
lean_dec(v_val_1550_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
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
lean_object* v_a_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1589_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1590_ = lean_unsigned_to_nat(3u);
v___x_1591_ = lean_array_fget_borrowed(v_val_1550_, v___x_1590_);
lean_inc(v___x_1591_);
v___x_1592_ = l_Lean_Json_getNat_x3f(v___x_1591_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1589_);
lean_dec(v_a_1577_);
lean_dec(v_a_1565_);
lean_dec(v_val_1550_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_a_1601_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1602_ = lean_unsigned_to_nat(5u);
v___x_1603_ = lean_nat_dec_eq(v___x_1551_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_val_1550_);
v___x_1604_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1605_, 0, v_a_1565_);
lean_ctor_set(v___x_1605_, 1, v_a_1577_);
lean_ctor_set(v___x_1605_, 2, v_a_1589_);
lean_ctor_set(v___x_1605_, 3, v_a_1601_);
lean_ctor_set(v___x_1605_, 4, v___x_1604_);
v_a_1547_ = v___x_1605_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_array_fget(v_val_1550_, v___x_1552_);
lean_dec(v_val_1550_);
v___x_1607_ = l_Lean_Json_getStr_x3f(v___x_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1601_);
lean_dec(v_a_1589_);
lean_dec(v_a_1577_);
lean_dec(v_a_1565_);
lean_dec(v_a_1493_);
lean_dec(v_v_1473_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1565_);
lean_ctor_set(v___x_1617_, 1, v_a_1577_);
lean_ctor_set(v___x_1617_, 2, v_a_1589_);
lean_ctor_set(v___x_1617_, 3, v_a_1601_);
lean_ctor_set(v___x_1617_, 4, v_a_1616_);
v_a_1547_ = v___x_1617_;
goto v___jp_1546_;
}
}
}
}
}
}
}
}
v___jp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1514_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1473_, v___x_1510_, v___x_1513_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_definition_x3f_1512_);
lean_dec(v_a_1493_);
lean_dec(v_m_1471_);
lean_dec_ref(v_toLocation_1470_);
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
lean_object* v_a_1523_; size_t v_sz_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1514_, 1);
v_sz_1524_ = lean_array_size(v_a_1523_);
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1494_, v_toLocation_1470_, v_sz_1524_, v___x_1525_, v_a_1523_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_definition_x3f_1512_);
lean_dec(v_a_1493_);
lean_dec(v_m_1471_);
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
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1545_; 
v_a_1535_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1537_ = v___x_1526_;
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_definition_x3f_1512_);
lean_ctor_set(v___x_1539_, 1, v_a_1535_);
v___x_1540_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1540_, v_a_1493_, v___x_1539_, v_m_1471_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1541_);
v___x_1543_ = v___x_1537_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
v___jp_1546_:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1547_);
v_definition_x3f_1512_ = v___x_1548_;
goto v___jp_1511_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1628_, lean_object* v___f_1629_, lean_object* v_j_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Json_getObj_x3f(v_j_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v___f_1629_);
lean_dec_ref(v___x_1628_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1641_ = lean_box(1);
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1628_, v___f_1629_, v___x_1641_, v_a_1640_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1649_, lean_object* v_k_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = l_Lean_Json_getObjValD(v_j_1649_, v_k_1650_);
v___x_1652_ = l_Lean_Json_getNat_x3f(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1653_, lean_object* v_k_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1653_, v_k_1654_);
lean_dec_ref(v_k_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1656_, lean_object* v_k_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = l_Lean_Json_getObjValD(v_j_1656_, v_k_1657_);
v___x_1659_ = l_Lean_Json_getBool_x3f(v___x_1658_);
lean_dec(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1660_, v_k_1661_);
lean_dec_ref(v_k_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1665_, size_t v_i_1666_, lean_object* v_bs_1667_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_usize_dec_lt(v_i_1666_, v_sz_1665_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v_bs_1667_);
return v___x_1671_;
}
else
{
lean_object* v_v_1672_; 
v_v_1672_ = lean_array_uget_borrowed(v_bs_1667_, v_i_1666_);
if (lean_obj_tag(v_v_1672_) == 4)
{
lean_object* v_elems_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_elems_1673_ = lean_ctor_get(v_v_1672_, 0);
v___x_1674_ = lean_array_get_size(v_elems_1673_);
v___x_1675_ = lean_unsigned_to_nat(4u);
v___x_1676_ = lean_nat_dec_eq(v___x_1674_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_dec_ref(v_bs_1667_);
goto v___jp_1668_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_array_fget_borrowed(v_elems_1673_, v___x_1677_);
lean_inc(v___x_1678_);
v___x_1679_ = l_Lean_Json_getStr_x3f(v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_bs_1667_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1688_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_array_fget_borrowed(v_elems_1673_, v___x_1689_);
v___x_1691_ = l_Lean_Json_getBool_x3f(v___x_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_a_1688_);
lean_dec_ref(v_bs_1667_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1700_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1701_ = lean_unsigned_to_nat(2u);
v___x_1702_ = lean_array_fget_borrowed(v_elems_1673_, v___x_1701_);
v___x_1703_ = l_Lean_Json_getBool_x3f(v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_a_1700_);
lean_dec(v_a_1688_);
lean_dec_ref(v_bs_1667_);
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1712_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1714_ = lean_array_fget_borrowed(v_elems_1673_, v___x_1713_);
v___x_1715_ = l_Lean_Json_getBool_x3f(v___x_1714_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1712_);
lean_dec(v_a_1700_);
lean_dec(v_a_1688_);
lean_dec_ref(v_bs_1667_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v_bs_x27_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; uint8_t v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; lean_object* v___x_1732_; 
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1715_, 1);
v_bs_x27_1725_ = lean_array_uset(v_bs_1667_, v_i_1666_, v___x_1677_);
v___x_1726_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1726_, 0, v_a_1688_);
v___x_1727_ = lean_unbox(v_a_1700_);
lean_dec(v_a_1700_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*1, v___x_1727_);
v___x_1728_ = lean_unbox(v_a_1712_);
lean_dec(v_a_1712_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*1 + 1, v___x_1728_);
v___x_1729_ = lean_unbox(v_a_1724_);
lean_dec(v_a_1724_);
lean_ctor_set_uint8(v___x_1726_, sizeof(void*)*1 + 2, v___x_1729_);
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1666_, v___x_1730_);
v___x_1732_ = lean_array_uset(v_bs_x27_1725_, v_i_1666_, v___x_1726_);
v_i_1666_ = v___x_1731_;
v_bs_1667_ = v___x_1732_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1667_);
goto v___jp_1668_;
}
}
v___jp_1668_:
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1742_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 4)
{
lean_object* v_elems_1743_; size_t v_sz_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v_elems_1743_ = lean_ctor_get(v_x_1742_, 0);
lean_inc_ref(v_elems_1743_);
lean_dec_ref_known(v_x_1742_, 1);
v_sz_1744_ = lean_array_size(v_elems_1743_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1744_, v___x_1745_, v_elems_1743_);
return v___x_1746_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1747_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1748_ = lean_unsigned_to_nat(80u);
v___x_1749_ = l_Lean_Json_pretty(v_x_1742_, v___x_1748_);
v___x_1750_ = lean_string_append(v___x_1747_, v___x_1749_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1754_, lean_object* v_k_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = l_Lean_Json_getObjValD(v_j_1754_, v_k_1755_);
v___x_1757_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1758_, lean_object* v_k_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1758_, v_k_1759_);
lean_dec_ref(v_k_1759_);
return v_res_1760_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = 1;
v___x_1770_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1770_, v___x_1769_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1774_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1775_ = lean_string_append(v___x_1774_, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = 1;
v___x_1779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1780_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1782_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1783_ = lean_string_append(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1786_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1787_ = lean_string_append(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = 1;
v___x_1792_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1793_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1795_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1796_ = lean_string_append(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1798_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1799_ = lean_string_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 1;
v___x_1804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1807_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1811_ = lean_string_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1812_);
v___x_1814_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1812_, v___x_1813_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_json_1812_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1820_ = lean_string_append(v___x_1819_, v_a_1815_);
lean_dec(v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_json_1812_);
v_a_1825_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1814_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1814_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 0);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_a_1833_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1812_);
v___x_1835_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1812_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1833_);
lean_dec(v_json_1812_);
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
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
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
lean_dec(v_a_1833_);
lean_dec(v_json_1812_);
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
v___x_1855_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1856_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1812_, v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1854_);
lean_dec(v_a_1833_);
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
v___x_1861_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
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
lean_dec(v_a_1833_);
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
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1884_; 
v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1877_ = v___x_1856_;
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1856_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1879_, 0, v_a_1833_);
lean_ctor_set(v___x_1879_, 1, v_a_1875_);
v___x_1880_ = lean_unbox(v_a_1854_);
lean_dec(v_a_1854_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*2, v___x_1880_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1879_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1887_, size_t v_i_1888_, lean_object* v_bs_1889_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_lt(v_i_1888_, v_sz_1887_);
if (v___x_1890_ == 0)
{
return v_bs_1889_;
}
else
{
lean_object* v_v_1891_; lean_object* v_module_1892_; uint8_t v_isPrivate_1893_; uint8_t v_isAll_1894_; uint8_t v_isMeta_1895_; lean_object* v___x_1896_; lean_object* v_bs_x27_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; lean_object* v___x_1911_; 
v_v_1891_ = lean_array_uget_borrowed(v_bs_1889_, v_i_1888_);
v_module_1892_ = lean_ctor_get(v_v_1891_, 0);
lean_inc_ref(v_module_1892_);
v_isPrivate_1893_ = lean_ctor_get_uint8(v_v_1891_, sizeof(void*)*1);
v_isAll_1894_ = lean_ctor_get_uint8(v_v_1891_, sizeof(void*)*1 + 1);
v_isMeta_1895_ = lean_ctor_get_uint8(v_v_1891_, sizeof(void*)*1 + 2);
v___x_1896_ = lean_unsigned_to_nat(0u);
v_bs_x27_1897_ = lean_array_uset(v_bs_1889_, v_i_1888_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_module_1892_);
v___x_1899_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1899_, 0, v_isPrivate_1893_);
v___x_1900_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1900_, 0, v_isAll_1894_);
v___x_1901_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1901_, 0, v_isMeta_1895_);
v___x_1902_ = lean_unsigned_to_nat(4u);
v___x_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___x_1904_ = lean_array_push(v___x_1903_, v___x_1898_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1899_);
v___x_1906_ = lean_array_push(v___x_1905_, v___x_1900_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1901_);
v___x_1908_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1888_, v___x_1909_);
v___x_1911_ = lean_array_uset(v_bs_x27_1897_, v_i_1888_, v___x_1908_);
v_i_1888_ = v___x_1910_;
v_bs_1889_ = v___x_1911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1913_, lean_object* v_i_1914_, lean_object* v_bs_1915_){
_start:
{
size_t v_sz_boxed_1916_; size_t v_i_boxed_1917_; lean_object* v_res_1918_; 
v_sz_boxed_1916_ = lean_unbox_usize(v_sz_1913_);
lean_dec(v_sz_1913_);
v_i_boxed_1917_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1916_, v_i_boxed_1917_, v_bs_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1919_){
_start:
{
size_t v_sz_1920_; size_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_sz_1920_ = lean_array_size(v_a_1919_);
v___x_1921_ = ((size_t)0ULL);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1920_, v___x_1921_, v_a_1919_);
v___x_1923_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
if (lean_obj_tag(v_a_1924_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_array_to_list(v_a_1925_);
return v___x_1926_;
}
else
{
lean_object* v_head_1927_; lean_object* v_tail_1928_; lean_object* v___x_1929_; 
v_head_1927_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_head_1927_);
v_tail_1928_ = lean_ctor_get(v_a_1924_, 1);
lean_inc(v_tail_1928_);
lean_dec_ref_known(v_a_1924_, 2);
v___x_1929_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1925_, v_head_1927_);
v_a_1924_ = v_tail_1928_;
v_a_1925_ = v___x_1929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1933_){
_start:
{
lean_object* v_version_1934_; uint8_t v_isSetupFailure_1935_; lean_object* v_directImports_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_version_1934_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_version_1934_);
v_isSetupFailure_1935_ = lean_ctor_get_uint8(v_x_1933_, sizeof(void*)*2);
v_directImports_1936_ = lean_ctor_get(v_x_1933_, 1);
lean_inc_ref(v_directImports_1936_);
lean_dec_ref(v_x_1933_);
v___x_1937_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1938_ = l_Lean_JsonNumber_fromNat(v_version_1934_);
v___x_1939_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1937_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1944_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1944_, 0, v_isSetupFailure_1935_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v___x_1941_);
v___x_1947_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1948_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1936_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1941_);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1941_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1946_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1942_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1955_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1953_, v___x_1954_);
v___x_1956_ = l_Lean_Json_mkObj(v___x_1955_);
lean_dec(v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1959_, lean_object* v_v_1960_, lean_object* v_t_1961_){
_start:
{
if (lean_obj_tag(v_t_1961_) == 0)
{
lean_object* v_size_1962_; lean_object* v_k_1963_; lean_object* v_v_1964_; lean_object* v_l_1965_; lean_object* v_r_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2246_; 
v_size_1962_ = lean_ctor_get(v_t_1961_, 0);
v_k_1963_ = lean_ctor_get(v_t_1961_, 1);
v_v_1964_ = lean_ctor_get(v_t_1961_, 2);
v_l_1965_ = lean_ctor_get(v_t_1961_, 3);
v_r_1966_ = lean_ctor_get(v_t_1961_, 4);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_t_1961_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_1968_ = v_t_1961_;
v_isShared_1969_ = v_isSharedCheck_2246_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_r_1966_);
lean_inc(v_l_1965_);
lean_inc(v_v_1964_);
lean_inc(v_k_1963_);
lean_inc(v_size_1962_);
lean_dec(v_t_1961_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2246_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_string_compare(v_k_1959_, v_k_1963_);
switch(v___x_1970_)
{
case 0:
{
lean_object* v_impl_1971_; lean_object* v___x_1972_; 
lean_dec(v_size_1962_);
v_impl_1971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1959_, v_v_1960_, v_l_1965_);
v___x_1972_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1966_) == 0)
{
lean_object* v_size_1973_; lean_object* v_size_1974_; lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v_l_1977_; lean_object* v_r_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_size_1973_ = lean_ctor_get(v_r_1966_, 0);
v_size_1974_ = lean_ctor_get(v_impl_1971_, 0);
lean_inc(v_size_1974_);
v_k_1975_ = lean_ctor_get(v_impl_1971_, 1);
lean_inc(v_k_1975_);
v_v_1976_ = lean_ctor_get(v_impl_1971_, 2);
lean_inc(v_v_1976_);
v_l_1977_ = lean_ctor_get(v_impl_1971_, 3);
lean_inc(v_l_1977_);
v_r_1978_ = lean_ctor_get(v_impl_1971_, 4);
lean_inc(v_r_1978_);
v___x_1979_ = lean_unsigned_to_nat(3u);
v___x_1980_ = lean_nat_mul(v___x_1979_, v_size_1973_);
v___x_1981_ = lean_nat_dec_lt(v___x_1980_, v_size_1974_);
lean_dec(v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_r_1978_);
lean_dec(v_l_1977_);
lean_dec(v_v_1976_);
lean_dec(v_k_1975_);
v___x_1982_ = lean_nat_add(v___x_1972_, v_size_1974_);
lean_dec(v_size_1974_);
v___x_1983_ = lean_nat_add(v___x_1982_, v_size_1973_);
lean_dec(v___x_1982_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 3, v_impl_1971_);
lean_ctor_set(v___x_1968_, 0, v___x_1983_);
v___x_1985_ = v___x_1968_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_impl_1971_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_r_1966_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2052_; 
v_isSharedCheck_2052_ = !lean_is_exclusive(v_impl_1971_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2053_ = lean_ctor_get(v_impl_1971_, 4);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_impl_1971_, 3);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_impl_1971_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_impl_1971_, 1);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_impl_1971_, 0);
lean_dec(v_unused_2057_);
v___x_1988_ = v_impl_1971_;
v_isShared_1989_ = v_isSharedCheck_2052_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v_impl_1971_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2052_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_size_1990_; lean_object* v_size_1991_; lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v_l_1994_; lean_object* v_r_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_size_1990_ = lean_ctor_get(v_l_1977_, 0);
v_size_1991_ = lean_ctor_get(v_r_1978_, 0);
v_k_1992_ = lean_ctor_get(v_r_1978_, 1);
v_v_1993_ = lean_ctor_get(v_r_1978_, 2);
v_l_1994_ = lean_ctor_get(v_r_1978_, 3);
v_r_1995_ = lean_ctor_get(v_r_1978_, 4);
v___x_1996_ = lean_unsigned_to_nat(2u);
v___x_1997_ = lean_nat_mul(v___x_1996_, v_size_1990_);
v___x_1998_ = lean_nat_dec_lt(v_size_1991_, v___x_1997_);
lean_dec(v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2027_; 
lean_inc(v_r_1995_);
lean_inc(v_l_1994_);
lean_inc(v_v_1993_);
lean_inc(v_k_1992_);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_r_1978_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; 
v_unused_2028_ = lean_ctor_get(v_r_1978_, 4);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_r_1978_, 3);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1978_, 2);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1978_, 1);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1978_, 0);
lean_dec(v_unused_2032_);
v___x_2000_ = v_r_1978_;
v_isShared_2001_ = v_isSharedCheck_2027_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_r_1978_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2027_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___x_2015_; lean_object* v___y_2017_; 
v___x_2002_ = lean_nat_add(v___x_1972_, v_size_1974_);
lean_dec(v_size_1974_);
v___x_2003_ = lean_nat_add(v___x_2002_, v_size_1973_);
lean_dec(v___x_2002_);
v___x_2015_ = lean_nat_add(v___x_1972_, v_size_1990_);
if (lean_obj_tag(v_l_1994_) == 0)
{
lean_object* v_size_2025_; 
v_size_2025_ = lean_ctor_get(v_l_1994_, 0);
lean_inc(v_size_2025_);
v___y_2017_ = v_size_2025_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___y_2017_ = v___x_2026_;
goto v___jp_2016_;
}
v___jp_2004_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_nat_add(v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 4, v_r_1966_);
lean_ctor_set(v___x_2000_, 3, v_r_1995_);
lean_ctor_set(v___x_2000_, 2, v_v_1964_);
lean_ctor_set(v___x_2000_, 1, v_k_1963_);
lean_ctor_set(v___x_2000_, 0, v___x_2008_);
v___x_2010_ = v___x_2000_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_r_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_r_1966_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2010_);
lean_ctor_set(v___x_1988_, 3, v___y_2005_);
lean_ctor_set(v___x_1988_, 2, v_v_1993_);
lean_ctor_set(v___x_1988_, 1, v_k_1992_);
lean_ctor_set(v___x_1988_, 0, v___x_2003_);
v___x_2012_ = v___x_1988_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v___y_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
v___jp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_nat_add(v___x_2015_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec(v___x_2015_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_l_1994_);
lean_ctor_set(v___x_1968_, 3, v_l_1977_);
lean_ctor_set(v___x_1968_, 2, v_v_1976_);
lean_ctor_set(v___x_1968_, 1, v_k_1975_);
lean_ctor_set(v___x_1968_, 0, v___x_2018_);
v___x_2020_ = v___x_1968_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_l_1977_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_l_1994_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_nat_add(v___x_1972_, v_size_1973_);
if (lean_obj_tag(v_r_1995_) == 0)
{
lean_object* v_size_2022_; 
v_size_2022_ = lean_ctor_get(v_r_1995_, 0);
lean_inc(v_size_2022_);
v___y_2005_ = v___x_2020_;
v___y_2006_ = v___x_2021_;
v___y_2007_ = v_size_2022_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_unsigned_to_nat(0u);
v___y_2005_ = v___x_2020_;
v___y_2006_ = v___x_2021_;
v___y_2007_ = v___x_2023_;
goto v___jp_2004_;
}
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
lean_del_object(v___x_1968_);
v___x_2033_ = lean_nat_add(v___x_1972_, v_size_1974_);
lean_dec(v_size_1974_);
v___x_2034_ = lean_nat_add(v___x_2033_, v_size_1973_);
lean_dec(v___x_2033_);
v___x_2035_ = lean_nat_add(v___x_1972_, v_size_1973_);
v___x_2036_ = lean_nat_add(v___x_2035_, v_size_1991_);
lean_dec(v___x_2035_);
lean_inc_ref(v_r_1966_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_r_1966_);
lean_ctor_set(v___x_1988_, 3, v_r_1978_);
lean_ctor_set(v___x_1988_, 2, v_v_1964_);
lean_ctor_set(v___x_1988_, 1, v_k_1963_);
lean_ctor_set(v___x_1988_, 0, v___x_2036_);
v___x_2038_ = v___x_1988_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_r_1978_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_r_1966_);
v___x_2038_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v_r_1966_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2046_ = lean_ctor_get(v_r_1966_, 4);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_r_1966_, 3);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_r_1966_, 2);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_r_1966_, 1);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_r_1966_, 0);
lean_dec(v_unused_2050_);
v___x_2040_ = v_r_1966_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_r_1966_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 4, v___x_2038_);
lean_ctor_set(v___x_2040_, 3, v_l_1977_);
lean_ctor_set(v___x_2040_, 2, v_v_1976_);
lean_ctor_set(v___x_2040_, 1, v_k_1975_);
lean_ctor_set(v___x_2040_, 0, v___x_2034_);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1977_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v___x_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2058_; 
v_l_2058_ = lean_ctor_get(v_impl_1971_, 3);
lean_inc(v_l_2058_);
if (lean_obj_tag(v_l_2058_) == 0)
{
lean_object* v_r_2059_; lean_object* v_k_2060_; lean_object* v_v_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v_r_2059_ = lean_ctor_get(v_impl_1971_, 4);
v_k_2060_ = lean_ctor_get(v_impl_1971_, 1);
v_v_2061_ = lean_ctor_get(v_impl_1971_, 2);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_impl_1971_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; lean_object* v_unused_2074_; 
v_unused_2073_ = lean_ctor_get(v_impl_1971_, 3);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_impl_1971_, 0);
lean_dec(v_unused_2074_);
v___x_2063_ = v_impl_1971_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_r_2059_);
lean_inc(v_v_2061_);
lean_inc(v_k_2060_);
lean_dec(v_impl_1971_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2059_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 3, v_r_2059_);
lean_ctor_set(v___x_2063_, 2, v_v_1964_);
lean_ctor_set(v___x_2063_, 1, v_k_1963_);
lean_ctor_set(v___x_2063_, 0, v___x_1972_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_r_2059_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_r_2059_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_2067_);
lean_ctor_set(v___x_1968_, 3, v_l_2058_);
lean_ctor_set(v___x_1968_, 2, v_v_2061_);
lean_ctor_set(v___x_1968_, 1, v_k_2060_);
lean_ctor_set(v___x_1968_, 0, v___x_2065_);
v___x_2069_ = v___x_1968_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_2060_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_2061_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_l_2058_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_r_2075_; 
v_r_2075_ = lean_ctor_get(v_impl_1971_, 4);
lean_inc(v_r_2075_);
if (lean_obj_tag(v_r_2075_) == 0)
{
lean_object* v_k_2076_; lean_object* v_v_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2100_; 
v_k_2076_ = lean_ctor_get(v_impl_1971_, 1);
v_v_2077_ = lean_ctor_get(v_impl_1971_, 2);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_impl_1971_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; lean_object* v_unused_2102_; lean_object* v_unused_2103_; 
v_unused_2101_ = lean_ctor_get(v_impl_1971_, 4);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_impl_1971_, 3);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v_impl_1971_, 0);
lean_dec(v_unused_2103_);
v___x_2079_ = v_impl_1971_;
v_isShared_2080_ = v_isSharedCheck_2100_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_v_2077_);
lean_inc(v_k_2076_);
lean_dec(v_impl_1971_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2100_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_k_2081_; lean_object* v_v_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2096_; 
v_k_2081_ = lean_ctor_get(v_r_2075_, 1);
v_v_2082_ = lean_ctor_get(v_r_2075_, 2);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_r_2075_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2097_ = lean_ctor_get(v_r_2075_, 4);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_r_2075_, 3);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_r_2075_, 0);
lean_dec(v_unused_2099_);
v___x_2084_ = v_r_2075_;
v_isShared_2085_ = v_isSharedCheck_2096_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_v_2082_);
lean_inc(v_k_2081_);
lean_dec(v_r_2075_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2096_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_unsigned_to_nat(3u);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 4, v_l_2058_);
lean_ctor_set(v___x_2084_, 3, v_l_2058_);
lean_ctor_set(v___x_2084_, 2, v_v_2077_);
lean_ctor_set(v___x_2084_, 1, v_k_2076_);
lean_ctor_set(v___x_2084_, 0, v___x_1972_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_k_2076_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_v_2077_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_l_2058_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_l_2058_);
v___x_2088_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 4, v_l_2058_);
lean_ctor_set(v___x_2079_, 2, v_v_1964_);
lean_ctor_set(v___x_2079_, 1, v_k_1963_);
lean_ctor_set(v___x_2079_, 0, v___x_1972_);
v___x_2090_ = v___x_2079_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_l_2058_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v_l_2058_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_2090_);
lean_ctor_set(v___x_1968_, 3, v___x_2088_);
lean_ctor_set(v___x_1968_, 2, v_v_2082_);
lean_ctor_set(v___x_1968_, 1, v_k_2081_);
lean_ctor_set(v___x_1968_, 0, v___x_2086_);
v___x_2092_ = v___x_1968_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_k_2081_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_v_2082_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_unsigned_to_nat(2u);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_r_2075_);
lean_ctor_set(v___x_1968_, 3, v_impl_1971_);
lean_ctor_set(v___x_1968_, 0, v___x_2104_);
v___x_2106_ = v___x_1968_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_impl_1971_);
lean_ctor_set(v_reuseFailAlloc_2107_, 4, v_r_2075_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2109_; 
lean_dec(v_v_1964_);
lean_dec(v_k_1963_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 2, v_v_1960_);
lean_ctor_set(v___x_1968_, 1, v_k_1959_);
v___x_2109_ = v___x_1968_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_size_1962_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_k_1959_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_v_1960_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_l_1965_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_r_1966_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
default: 
{
lean_object* v_impl_2111_; lean_object* v___x_2112_; 
lean_dec(v_size_1962_);
v_impl_2111_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1959_, v_v_1960_, v_r_1966_);
v___x_2112_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1965_) == 0)
{
lean_object* v_size_2113_; lean_object* v_size_2114_; lean_object* v_k_2115_; lean_object* v_v_2116_; lean_object* v_l_2117_; lean_object* v_r_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_size_2113_ = lean_ctor_get(v_l_1965_, 0);
v_size_2114_ = lean_ctor_get(v_impl_2111_, 0);
lean_inc(v_size_2114_);
v_k_2115_ = lean_ctor_get(v_impl_2111_, 1);
lean_inc(v_k_2115_);
v_v_2116_ = lean_ctor_get(v_impl_2111_, 2);
lean_inc(v_v_2116_);
v_l_2117_ = lean_ctor_get(v_impl_2111_, 3);
lean_inc(v_l_2117_);
v_r_2118_ = lean_ctor_get(v_impl_2111_, 4);
lean_inc(v_r_2118_);
v___x_2119_ = lean_unsigned_to_nat(3u);
v___x_2120_ = lean_nat_mul(v___x_2119_, v_size_2113_);
v___x_2121_ = lean_nat_dec_lt(v___x_2120_, v_size_2114_);
lean_dec(v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_r_2118_);
lean_dec(v_l_2117_);
lean_dec(v_v_2116_);
lean_dec(v_k_2115_);
v___x_2122_ = lean_nat_add(v___x_2112_, v_size_2113_);
v___x_2123_ = lean_nat_add(v___x_2122_, v_size_2114_);
lean_dec(v_size_2114_);
lean_dec(v___x_2122_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_impl_2111_);
lean_ctor_set(v___x_1968_, 0, v___x_2123_);
v___x_2125_ = v___x_1968_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_l_1965_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_impl_2111_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2190_; 
v_isSharedCheck_2190_ = !lean_is_exclusive(v_impl_2111_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2191_ = lean_ctor_get(v_impl_2111_, 4);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_impl_2111_, 3);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_impl_2111_, 2);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_impl_2111_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_impl_2111_, 0);
lean_dec(v_unused_2195_);
v___x_2128_ = v_impl_2111_;
v_isShared_2129_ = v_isSharedCheck_2190_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v_impl_2111_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2190_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_size_2130_; lean_object* v_k_2131_; lean_object* v_v_2132_; lean_object* v_l_2133_; lean_object* v_r_2134_; lean_object* v_size_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v_size_2130_ = lean_ctor_get(v_l_2117_, 0);
v_k_2131_ = lean_ctor_get(v_l_2117_, 1);
v_v_2132_ = lean_ctor_get(v_l_2117_, 2);
v_l_2133_ = lean_ctor_get(v_l_2117_, 3);
v_r_2134_ = lean_ctor_get(v_l_2117_, 4);
v_size_2135_ = lean_ctor_get(v_r_2118_, 0);
v___x_2136_ = lean_unsigned_to_nat(2u);
v___x_2137_ = lean_nat_mul(v___x_2136_, v_size_2135_);
v___x_2138_ = lean_nat_dec_lt(v_size_2130_, v___x_2137_);
lean_dec(v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2166_; 
lean_inc(v_r_2134_);
lean_inc(v_l_2133_);
lean_inc(v_v_2132_);
lean_inc(v_k_2131_);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_l_2117_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; lean_object* v_unused_2171_; 
v_unused_2167_ = lean_ctor_get(v_l_2117_, 4);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_l_2117_, 3);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2117_, 2);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_l_2117_, 1);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_l_2117_, 0);
lean_dec(v_unused_2171_);
v___x_2140_ = v_l_2117_;
v_isShared_2141_ = v_isSharedCheck_2166_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_l_2117_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2166_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2156_; 
v___x_2142_ = lean_nat_add(v___x_2112_, v_size_2113_);
v___x_2143_ = lean_nat_add(v___x_2142_, v_size_2114_);
lean_dec(v_size_2114_);
if (lean_obj_tag(v_l_2133_) == 0)
{
lean_object* v_size_2164_; 
v_size_2164_ = lean_ctor_get(v_l_2133_, 0);
lean_inc(v_size_2164_);
v___y_2156_ = v_size_2164_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___y_2156_ = v___x_2165_;
goto v___jp_2155_;
}
v___jp_2144_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_nat_add(v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec(v___y_2146_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 4, v_r_2118_);
lean_ctor_set(v___x_2140_, 3, v_r_2134_);
lean_ctor_set(v___x_2140_, 2, v_v_2116_);
lean_ctor_set(v___x_2140_, 1, v_k_2115_);
lean_ctor_set(v___x_2140_, 0, v___x_2148_);
v___x_2150_ = v___x_2140_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_r_2134_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_r_2118_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v___x_2150_);
lean_ctor_set(v___x_2128_, 3, v___y_2145_);
lean_ctor_set(v___x_2128_, 2, v_v_2132_);
lean_ctor_set(v___x_2128_, 1, v_k_2131_);
lean_ctor_set(v___x_2128_, 0, v___x_2143_);
v___x_2152_ = v___x_2128_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2131_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2132_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v___y_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_nat_add(v___x_2142_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec(v___x_2142_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_l_2133_);
lean_ctor_set(v___x_1968_, 0, v___x_2157_);
v___x_2159_ = v___x_1968_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_1965_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2133_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_nat_add(v___x_2112_, v_size_2135_);
if (lean_obj_tag(v_r_2134_) == 0)
{
lean_object* v_size_2161_; 
v_size_2161_ = lean_ctor_get(v_r_2134_, 0);
lean_inc(v_size_2161_);
v___y_2145_ = v___x_2159_;
v___y_2146_ = v___x_2160_;
v___y_2147_ = v_size_2161_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_unsigned_to_nat(0u);
v___y_2145_ = v___x_2159_;
v___y_2146_ = v___x_2160_;
v___y_2147_ = v___x_2162_;
goto v___jp_2144_;
}
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_del_object(v___x_1968_);
v___x_2172_ = lean_nat_add(v___x_2112_, v_size_2113_);
v___x_2173_ = lean_nat_add(v___x_2172_, v_size_2114_);
lean_dec(v_size_2114_);
v___x_2174_ = lean_nat_add(v___x_2172_, v_size_2130_);
lean_dec(v___x_2172_);
lean_inc_ref(v_l_1965_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v_l_2117_);
lean_ctor_set(v___x_2128_, 3, v_l_1965_);
lean_ctor_set(v___x_2128_, 2, v_v_1964_);
lean_ctor_set(v___x_2128_, 1, v_k_1963_);
lean_ctor_set(v___x_2128_, 0, v___x_2174_);
v___x_2176_ = v___x_2128_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_l_1965_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_l_2117_);
v___x_2176_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_isSharedCheck_2183_ = !lean_is_exclusive(v_l_1965_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; lean_object* v_unused_2187_; lean_object* v_unused_2188_; 
v_unused_2184_ = lean_ctor_get(v_l_1965_, 4);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_l_1965_, 3);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_l_1965_, 2);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_l_1965_, 1);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_l_1965_, 0);
lean_dec(v_unused_2188_);
v___x_2178_ = v_l_1965_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_l_1965_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_r_2118_);
lean_ctor_set(v___x_2178_, 3, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v_v_2116_);
lean_ctor_set(v___x_2178_, 1, v_k_2115_);
lean_ctor_set(v___x_2178_, 0, v___x_2173_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_r_2118_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2196_; 
v_l_2196_ = lean_ctor_get(v_impl_2111_, 3);
lean_inc(v_l_2196_);
if (lean_obj_tag(v_l_2196_) == 0)
{
lean_object* v_r_2197_; lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2222_; 
v_r_2197_ = lean_ctor_get(v_impl_2111_, 4);
v_k_2198_ = lean_ctor_get(v_impl_2111_, 1);
v_v_2199_ = lean_ctor_get(v_impl_2111_, 2);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_impl_2111_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; 
v_unused_2223_ = lean_ctor_get(v_impl_2111_, 3);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_impl_2111_, 0);
lean_dec(v_unused_2224_);
v___x_2201_ = v_impl_2111_;
v_isShared_2202_ = v_isSharedCheck_2222_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_r_2197_);
lean_inc(v_v_2199_);
lean_inc(v_k_2198_);
lean_dec(v_impl_2111_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2222_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_k_2203_; lean_object* v_v_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2218_; 
v_k_2203_ = lean_ctor_get(v_l_2196_, 1);
v_v_2204_ = lean_ctor_get(v_l_2196_, 2);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_l_2196_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2219_ = lean_ctor_get(v_l_2196_, 4);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_l_2196_, 3);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_l_2196_, 0);
lean_dec(v_unused_2221_);
v___x_2206_ = v_l_2196_;
v_isShared_2207_ = v_isSharedCheck_2218_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_v_2204_);
lean_inc(v_k_2203_);
lean_dec(v_l_2196_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2218_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2197_, 2);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 4, v_r_2197_);
lean_ctor_set(v___x_2206_, 3, v_r_2197_);
lean_ctor_set(v___x_2206_, 2, v_v_1964_);
lean_ctor_set(v___x_2206_, 1, v_k_1963_);
lean_ctor_set(v___x_2206_, 0, v___x_2112_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_r_2197_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v_r_2197_);
v___x_2210_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
lean_inc(v_r_2197_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 3, v_r_2197_);
lean_ctor_set(v___x_2201_, 0, v___x_2112_);
v___x_2212_ = v___x_2201_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_k_2198_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_v_2199_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_r_2197_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v_r_2197_);
v___x_2212_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_2212_);
lean_ctor_set(v___x_1968_, 3, v___x_2210_);
lean_ctor_set(v___x_1968_, 2, v_v_2204_);
lean_ctor_set(v___x_1968_, 1, v_k_2203_);
lean_ctor_set(v___x_1968_, 0, v___x_2208_);
v___x_2214_ = v___x_1968_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_2203_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_2204_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
else
{
lean_object* v_r_2225_; 
v_r_2225_ = lean_ctor_get(v_impl_2111_, 4);
lean_inc(v_r_2225_);
if (lean_obj_tag(v_r_2225_) == 0)
{
lean_object* v_k_2226_; lean_object* v_v_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2238_; 
v_k_2226_ = lean_ctor_get(v_impl_2111_, 1);
v_v_2227_ = lean_ctor_get(v_impl_2111_, 2);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_impl_2111_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; lean_object* v_unused_2240_; lean_object* v_unused_2241_; 
v_unused_2239_ = lean_ctor_get(v_impl_2111_, 4);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v_impl_2111_, 3);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_impl_2111_, 0);
lean_dec(v_unused_2241_);
v___x_2229_ = v_impl_2111_;
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_v_2227_);
lean_inc(v_k_2226_);
lean_dec(v_impl_2111_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_unsigned_to_nat(3u);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 4, v_l_2196_);
lean_ctor_set(v___x_2229_, 2, v_v_1964_);
lean_ctor_set(v___x_2229_, 1, v_k_1963_);
lean_ctor_set(v___x_2229_, 0, v___x_2112_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_l_2196_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_l_2196_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_r_2225_);
lean_ctor_set(v___x_1968_, 3, v___x_2233_);
lean_ctor_set(v___x_1968_, 2, v_v_2227_);
lean_ctor_set(v___x_1968_, 1, v_k_2226_);
lean_ctor_set(v___x_1968_, 0, v___x_2231_);
v___x_2235_ = v___x_1968_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_2226_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_2227_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_r_2225_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_unsigned_to_nat(2u);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_impl_2111_);
lean_ctor_set(v___x_1968_, 3, v_r_2225_);
lean_ctor_set(v___x_1968_, 0, v___x_2242_);
v___x_2244_ = v___x_1968_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v_r_2225_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_impl_2111_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
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
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v_k_1959_);
lean_ctor_set(v___x_2248_, 2, v_v_1960_);
lean_ctor_set(v___x_2248_, 3, v_t_1961_);
lean_ctor_set(v___x_2248_, 4, v_t_1961_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2249_, lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2250_) == 0)
{
lean_object* v_k_2251_; lean_object* v_v_2252_; lean_object* v_l_2253_; lean_object* v_r_2254_; lean_object* v___x_2255_; 
v_k_2251_ = lean_ctor_get(v_x_2250_, 1);
lean_inc(v_k_2251_);
v_v_2252_ = lean_ctor_get(v_x_2250_, 2);
lean_inc(v_v_2252_);
v_l_2253_ = lean_ctor_get(v_x_2250_, 3);
lean_inc(v_l_2253_);
v_r_2254_ = lean_ctor_get(v_x_2250_, 4);
lean_inc(v_r_2254_);
lean_dec_ref_known(v_x_2250_, 5);
v___x_2255_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2249_, v_l_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec(v_r_2254_);
lean_dec(v_v_2252_);
lean_dec(v_k_2251_);
return v___x_2255_;
}
else
{
if (lean_obj_tag(v_v_2252_) == 4)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2370_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2370_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2370_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_elems_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_elems_2260_ = lean_ctor_get(v_v_2252_, 0);
lean_inc_ref(v_elems_2260_);
lean_dec_ref_known(v_v_2252_, 1);
v___x_2261_ = lean_array_get_size(v_elems_2260_);
v___x_2262_ = lean_unsigned_to_nat(8u);
v___x_2263_ = lean_nat_dec_eq(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v___x_2264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2265_ = l_Nat_reprFast(v___x_2261_);
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
lean_dec_ref(v___x_2265_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set_tag(v___x_2258_, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2266_);
v___x_2268_ = v___x_2258_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_del_object(v___x_2258_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2271_);
lean_inc(v___x_2272_);
v___x_2273_ = l_Lean_Json_getNat_x3f(v___x_2272_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_a_2282_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2283_);
lean_inc(v___x_2284_);
v___x_2285_ = l_Lean_Json_getNat_x3f(v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2295_ = lean_unsigned_to_nat(2u);
v___x_2296_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2295_);
lean_inc(v___x_2296_);
v___x_2297_ = l_Lean_Json_getNat_x3f(v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2306_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2307_ = lean_unsigned_to_nat(3u);
v___x_2308_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2307_);
lean_inc(v___x_2308_);
v___x_2309_ = l_Lean_Json_getNat_x3f(v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_a_2306_);
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2318_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2319_ = lean_unsigned_to_nat(4u);
v___x_2320_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2319_);
lean_inc(v___x_2320_);
v___x_2321_ = l_Lean_Json_getNat_x3f(v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2318_);
lean_dec(v_a_2306_);
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_a_2330_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2331_ = lean_unsigned_to_nat(5u);
v___x_2332_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2331_);
lean_inc(v___x_2332_);
v___x_2333_ = l_Lean_Json_getNat_x3f(v___x_2332_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2330_);
lean_dec(v_a_2318_);
lean_dec(v_a_2306_);
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
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
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_a_2342_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2343_ = lean_unsigned_to_nat(6u);
v___x_2344_ = lean_array_get_borrowed(v___x_2270_, v_elems_2260_, v___x_2343_);
lean_inc(v___x_2344_);
v___x_2345_ = l_Lean_Json_getNat_x3f(v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2342_);
lean_dec(v_a_2330_);
lean_dec(v_a_2318_);
lean_dec(v_a_2306_);
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec_ref(v_elems_2260_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2354_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2355_ = lean_unsigned_to_nat(7u);
v___x_2356_ = lean_array_get(v___x_2270_, v_elems_2260_, v___x_2355_);
lean_dec_ref(v_elems_2260_);
v___x_2357_ = l_Lean_Json_getNat_x3f(v___x_2356_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2354_);
lean_dec(v_a_2342_);
lean_dec(v_a_2330_);
lean_dec(v_a_2318_);
lean_dec(v_a_2306_);
lean_dec(v_a_2294_);
lean_dec(v_a_2282_);
lean_dec(v_a_2256_);
lean_dec(v_r_2254_);
lean_dec(v_k_2251_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2366_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2367_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2282_);
lean_ctor_set(v___x_2367_, 1, v_a_2294_);
lean_ctor_set(v___x_2367_, 2, v_a_2306_);
lean_ctor_set(v___x_2367_, 3, v_a_2318_);
lean_ctor_set(v___x_2367_, 4, v_a_2330_);
lean_ctor_set(v___x_2367_, 5, v_a_2342_);
lean_ctor_set(v___x_2367_, 6, v_a_2354_);
lean_ctor_set(v___x_2367_, 7, v_a_2366_);
v___x_2368_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2251_, v___x_2367_, v_a_2256_);
v_init_2249_ = v___x_2368_;
v_x_2250_ = v_r_2254_;
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
lean_object* v___x_2371_; 
lean_dec_ref_known(v___x_2255_, 1);
lean_dec(v_r_2254_);
lean_dec(v_v_2252_);
lean_dec(v_k_2251_);
v___x_2371_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2371_;
}
}
}
else
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_init_2249_);
return v___x_2372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2373_, lean_object* v_k_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = l_Lean_Json_getObjValD(v_j_2373_, v_k_2374_);
v___x_2376_ = l_Lean_Json_getObj_x3f(v___x_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2386_ = lean_box(1);
v___x_2387_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2386_, v_a_2385_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2388_, lean_object* v_k_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2388_, v_k_2389_);
lean_dec_ref(v_k_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2391_, size_t v_i_2392_, lean_object* v_bs_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_lt(v_i_2392_, v_sz_2391_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_bs_2393_);
return v___x_2395_;
}
else
{
lean_object* v_v_2396_; lean_object* v___x_2397_; lean_object* v_bs_x27_2398_; size_t v___x_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v_v_2396_ = lean_array_uget(v_bs_2393_, v_i_2392_);
v___x_2397_ = lean_unsigned_to_nat(0u);
v_bs_x27_2398_ = lean_array_uset(v_bs_2393_, v_i_2392_, v___x_2397_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_add(v_i_2392_, v___x_2399_);
v___x_2401_ = lean_array_uset(v_bs_x27_2398_, v_i_2392_, v_v_2396_);
v_i_2392_ = v___x_2400_;
v_bs_2393_ = v___x_2401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2403_, lean_object* v_i_2404_, lean_object* v_bs_2405_){
_start:
{
size_t v_sz_boxed_2406_; size_t v_i_boxed_2407_; lean_object* v_res_2408_; 
v_sz_boxed_2406_ = lean_unbox_usize(v_sz_2403_);
lean_dec(v_sz_2403_);
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2406_, v_i_boxed_2407_, v_bs_2405_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2409_){
_start:
{
if (lean_obj_tag(v_x_2409_) == 4)
{
lean_object* v_elems_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v_elems_2410_ = lean_ctor_get(v_x_2409_, 0);
lean_inc_ref(v_elems_2410_);
lean_dec_ref_known(v_x_2409_, 1);
v_sz_2411_ = lean_array_size(v_elems_2410_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2411_, v___x_2412_, v_elems_2410_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2414_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2415_ = lean_unsigned_to_nat(80u);
v___x_2416_ = l_Lean_Json_pretty(v_x_2409_, v___x_2415_);
v___x_2417_ = lean_string_append(v___x_2414_, v___x_2416_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2419_ = lean_string_append(v___x_2417_, v___x_2418_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2423_){
_start:
{
if (lean_obj_tag(v_x_2423_) == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2442_; 
v_a_2434_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2436_ = v___x_2425_;
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2425_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2442_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_a_2434_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2443_, lean_object* v_k_2444_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = l_Lean_Json_getObjValD(v_j_2443_, v_k_2444_);
v___x_2446_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2447_, lean_object* v_k_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2447_, v_k_2448_);
lean_dec_ref(v_k_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2450_, lean_object* v_v_2451_, lean_object* v_t_2452_){
_start:
{
if (lean_obj_tag(v_t_2452_) == 0)
{
lean_object* v_size_2453_; lean_object* v_k_2454_; lean_object* v_v_2455_; lean_object* v_l_2456_; lean_object* v_r_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2737_; 
v_size_2453_ = lean_ctor_get(v_t_2452_, 0);
v_k_2454_ = lean_ctor_get(v_t_2452_, 1);
v_v_2455_ = lean_ctor_get(v_t_2452_, 2);
v_l_2456_ = lean_ctor_get(v_t_2452_, 3);
v_r_2457_ = lean_ctor_get(v_t_2452_, 4);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_t_2452_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2459_ = v_t_2452_;
v_isShared_2460_ = v_isSharedCheck_2737_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_r_2457_);
lean_inc(v_l_2456_);
lean_inc(v_v_2455_);
lean_inc(v_k_2454_);
lean_inc(v_size_2453_);
lean_dec(v_t_2452_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2737_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2450_, v_k_2454_);
switch(v___x_2461_)
{
case 0:
{
lean_object* v_impl_2462_; lean_object* v___x_2463_; 
lean_dec(v_size_2453_);
v_impl_2462_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2450_, v_v_2451_, v_l_2456_);
v___x_2463_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2457_) == 0)
{
lean_object* v_size_2464_; lean_object* v_size_2465_; lean_object* v_k_2466_; lean_object* v_v_2467_; lean_object* v_l_2468_; lean_object* v_r_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_size_2464_ = lean_ctor_get(v_r_2457_, 0);
v_size_2465_ = lean_ctor_get(v_impl_2462_, 0);
lean_inc(v_size_2465_);
v_k_2466_ = lean_ctor_get(v_impl_2462_, 1);
lean_inc(v_k_2466_);
v_v_2467_ = lean_ctor_get(v_impl_2462_, 2);
lean_inc(v_v_2467_);
v_l_2468_ = lean_ctor_get(v_impl_2462_, 3);
lean_inc(v_l_2468_);
v_r_2469_ = lean_ctor_get(v_impl_2462_, 4);
lean_inc(v_r_2469_);
v___x_2470_ = lean_unsigned_to_nat(3u);
v___x_2471_ = lean_nat_mul(v___x_2470_, v_size_2464_);
v___x_2472_ = lean_nat_dec_lt(v___x_2471_, v_size_2465_);
lean_dec(v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_dec(v_r_2469_);
lean_dec(v_l_2468_);
lean_dec(v_v_2467_);
lean_dec(v_k_2466_);
v___x_2473_ = lean_nat_add(v___x_2463_, v_size_2465_);
lean_dec(v_size_2465_);
v___x_2474_ = lean_nat_add(v___x_2473_, v_size_2464_);
lean_dec(v___x_2473_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 3, v_impl_2462_);
lean_ctor_set(v___x_2459_, 0, v___x_2474_);
v___x_2476_ = v___x_2459_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_impl_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_r_2457_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v_impl_2462_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; lean_object* v_unused_2545_; lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2544_ = lean_ctor_get(v_impl_2462_, 4);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_impl_2462_, 3);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_impl_2462_, 2);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_impl_2462_, 1);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_impl_2462_, 0);
lean_dec(v_unused_2548_);
v___x_2479_ = v_impl_2462_;
v_isShared_2480_ = v_isSharedCheck_2543_;
goto v_resetjp_2478_;
}
else
{
lean_dec(v_impl_2462_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2543_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_size_2481_; lean_object* v_size_2482_; lean_object* v_k_2483_; lean_object* v_v_2484_; lean_object* v_l_2485_; lean_object* v_r_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_size_2481_ = lean_ctor_get(v_l_2468_, 0);
v_size_2482_ = lean_ctor_get(v_r_2469_, 0);
v_k_2483_ = lean_ctor_get(v_r_2469_, 1);
v_v_2484_ = lean_ctor_get(v_r_2469_, 2);
v_l_2485_ = lean_ctor_get(v_r_2469_, 3);
v_r_2486_ = lean_ctor_get(v_r_2469_, 4);
v___x_2487_ = lean_unsigned_to_nat(2u);
v___x_2488_ = lean_nat_mul(v___x_2487_, v_size_2481_);
v___x_2489_ = lean_nat_dec_lt(v_size_2482_, v___x_2488_);
lean_dec(v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2518_; 
lean_inc(v_r_2486_);
lean_inc(v_l_2485_);
lean_inc(v_v_2484_);
lean_inc(v_k_2483_);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_r_2469_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; lean_object* v_unused_2522_; lean_object* v_unused_2523_; 
v_unused_2519_ = lean_ctor_get(v_r_2469_, 4);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_r_2469_, 3);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_r_2469_, 2);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_r_2469_, 1);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_r_2469_, 0);
lean_dec(v_unused_2523_);
v___x_2491_ = v_r_2469_;
v_isShared_2492_ = v_isSharedCheck_2518_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v_r_2469_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2518_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___x_2506_; lean_object* v___y_2508_; 
v___x_2493_ = lean_nat_add(v___x_2463_, v_size_2465_);
lean_dec(v_size_2465_);
v___x_2494_ = lean_nat_add(v___x_2493_, v_size_2464_);
lean_dec(v___x_2493_);
v___x_2506_ = lean_nat_add(v___x_2463_, v_size_2481_);
if (lean_obj_tag(v_l_2485_) == 0)
{
lean_object* v_size_2516_; 
v_size_2516_ = lean_ctor_get(v_l_2485_, 0);
lean_inc(v_size_2516_);
v___y_2508_ = v_size_2516_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___y_2508_ = v___x_2517_;
goto v___jp_2507_;
}
v___jp_2495_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_nat_add(v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v_r_2457_);
lean_ctor_set(v___x_2491_, 3, v_r_2486_);
lean_ctor_set(v___x_2491_, 2, v_v_2455_);
lean_ctor_set(v___x_2491_, 1, v_k_2454_);
lean_ctor_set(v___x_2491_, 0, v___x_2499_);
v___x_2501_ = v___x_2491_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_r_2486_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_r_2457_);
v___x_2501_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2503_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v___x_2501_);
lean_ctor_set(v___x_2479_, 3, v___y_2496_);
lean_ctor_set(v___x_2479_, 2, v_v_2484_);
lean_ctor_set(v___x_2479_, 1, v_k_2483_);
lean_ctor_set(v___x_2479_, 0, v___x_2494_);
v___x_2503_ = v___x_2479_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_k_2483_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_v_2484_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v___y_2496_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_nat_add(v___x_2506_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec(v___x_2506_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_l_2485_);
lean_ctor_set(v___x_2459_, 3, v_l_2468_);
lean_ctor_set(v___x_2459_, 2, v_v_2467_);
lean_ctor_set(v___x_2459_, 1, v_k_2466_);
lean_ctor_set(v___x_2459_, 0, v___x_2509_);
v___x_2511_ = v___x_2459_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_2466_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_2467_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_l_2468_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_l_2485_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_nat_add(v___x_2463_, v_size_2464_);
if (lean_obj_tag(v_r_2486_) == 0)
{
lean_object* v_size_2513_; 
v_size_2513_ = lean_ctor_get(v_r_2486_, 0);
lean_inc(v_size_2513_);
v___y_2496_ = v___x_2511_;
v___y_2497_ = v___x_2512_;
v___y_2498_ = v_size_2513_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___y_2496_ = v___x_2511_;
v___y_2497_ = v___x_2512_;
v___y_2498_ = v___x_2514_;
goto v___jp_2495_;
}
}
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_del_object(v___x_2459_);
v___x_2524_ = lean_nat_add(v___x_2463_, v_size_2465_);
lean_dec(v_size_2465_);
v___x_2525_ = lean_nat_add(v___x_2524_, v_size_2464_);
lean_dec(v___x_2524_);
v___x_2526_ = lean_nat_add(v___x_2463_, v_size_2464_);
v___x_2527_ = lean_nat_add(v___x_2526_, v_size_2482_);
lean_dec(v___x_2526_);
lean_inc_ref(v_r_2457_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_r_2457_);
lean_ctor_set(v___x_2479_, 3, v_r_2469_);
lean_ctor_set(v___x_2479_, 2, v_v_2455_);
lean_ctor_set(v___x_2479_, 1, v_k_2454_);
lean_ctor_set(v___x_2479_, 0, v___x_2527_);
v___x_2529_ = v___x_2479_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_r_2469_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_r_2457_);
v___x_2529_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_isSharedCheck_2536_ = !lean_is_exclusive(v_r_2457_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; 
v_unused_2537_ = lean_ctor_get(v_r_2457_, 4);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_r_2457_, 3);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_r_2457_, 2);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_r_2457_, 1);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_r_2457_, 0);
lean_dec(v_unused_2541_);
v___x_2531_ = v_r_2457_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_dec(v_r_2457_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v___x_2529_);
lean_ctor_set(v___x_2531_, 3, v_l_2468_);
lean_ctor_set(v___x_2531_, 2, v_v_2467_);
lean_ctor_set(v___x_2531_, 1, v_k_2466_);
lean_ctor_set(v___x_2531_, 0, v___x_2525_);
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2466_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2467_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_l_2468_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v___x_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2549_; 
v_l_2549_ = lean_ctor_get(v_impl_2462_, 3);
lean_inc(v_l_2549_);
if (lean_obj_tag(v_l_2549_) == 0)
{
lean_object* v_r_2550_; lean_object* v_k_2551_; lean_object* v_v_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2563_; 
v_r_2550_ = lean_ctor_get(v_impl_2462_, 4);
v_k_2551_ = lean_ctor_get(v_impl_2462_, 1);
v_v_2552_ = lean_ctor_get(v_impl_2462_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_impl_2462_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; 
v_unused_2564_ = lean_ctor_get(v_impl_2462_, 3);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_impl_2462_, 0);
lean_dec(v_unused_2565_);
v___x_2554_ = v_impl_2462_;
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_r_2550_);
lean_inc(v_v_2552_);
lean_inc(v_k_2551_);
lean_dec(v_impl_2462_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2550_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 3, v_r_2550_);
lean_ctor_set(v___x_2554_, 2, v_v_2455_);
lean_ctor_set(v___x_2554_, 1, v_k_2454_);
lean_ctor_set(v___x_2554_, 0, v___x_2463_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2550_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v___x_2558_);
lean_ctor_set(v___x_2459_, 3, v_l_2549_);
lean_ctor_set(v___x_2459_, 2, v_v_2552_);
lean_ctor_set(v___x_2459_, 1, v_k_2551_);
lean_ctor_set(v___x_2459_, 0, v___x_2556_);
v___x_2560_ = v___x_2459_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2551_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2552_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_l_2549_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_r_2566_; 
v_r_2566_ = lean_ctor_get(v_impl_2462_, 4);
lean_inc(v_r_2566_);
if (lean_obj_tag(v_r_2566_) == 0)
{
lean_object* v_k_2567_; lean_object* v_v_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2591_; 
v_k_2567_ = lean_ctor_get(v_impl_2462_, 1);
v_v_2568_ = lean_ctor_get(v_impl_2462_, 2);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_impl_2462_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; lean_object* v_unused_2593_; lean_object* v_unused_2594_; 
v_unused_2592_ = lean_ctor_get(v_impl_2462_, 4);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_impl_2462_, 3);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_impl_2462_, 0);
lean_dec(v_unused_2594_);
v___x_2570_ = v_impl_2462_;
v_isShared_2571_ = v_isSharedCheck_2591_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_v_2568_);
lean_inc(v_k_2567_);
lean_dec(v_impl_2462_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2591_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_k_2572_; lean_object* v_v_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2587_; 
v_k_2572_ = lean_ctor_get(v_r_2566_, 1);
v_v_2573_ = lean_ctor_get(v_r_2566_, 2);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_r_2566_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2588_ = lean_ctor_get(v_r_2566_, 4);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_r_2566_, 3);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v_r_2566_, 0);
lean_dec(v_unused_2590_);
v___x_2575_ = v_r_2566_;
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_v_2573_);
lean_inc(v_k_2572_);
lean_dec(v_r_2566_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2587_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_unsigned_to_nat(3u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2549_);
lean_ctor_set(v___x_2575_, 3, v_l_2549_);
lean_ctor_set(v___x_2575_, 2, v_v_2568_);
lean_ctor_set(v___x_2575_, 1, v_k_2567_);
lean_ctor_set(v___x_2575_, 0, v___x_2463_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_k_2567_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_v_2568_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_l_2549_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_l_2549_);
v___x_2579_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 4, v_l_2549_);
lean_ctor_set(v___x_2570_, 2, v_v_2455_);
lean_ctor_set(v___x_2570_, 1, v_k_2454_);
lean_ctor_set(v___x_2570_, 0, v___x_2463_);
v___x_2581_ = v___x_2570_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_l_2549_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_l_2549_);
v___x_2581_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v___x_2581_);
lean_ctor_set(v___x_2459_, 3, v___x_2579_);
lean_ctor_set(v___x_2459_, 2, v_v_2573_);
lean_ctor_set(v___x_2459_, 1, v_k_2572_);
lean_ctor_set(v___x_2459_, 0, v___x_2577_);
v___x_2583_ = v___x_2459_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2573_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_unsigned_to_nat(2u);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_r_2566_);
lean_ctor_set(v___x_2459_, 3, v_impl_2462_);
lean_ctor_set(v___x_2459_, 0, v___x_2595_);
v___x_2597_ = v___x_2459_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_impl_2462_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2566_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2600_; 
lean_dec(v_v_2455_);
lean_dec(v_k_2454_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 2, v_v_2451_);
lean_ctor_set(v___x_2459_, 1, v_k_2450_);
v___x_2600_ = v___x_2459_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_size_2453_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_l_2456_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2457_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
default: 
{
lean_object* v_impl_2602_; lean_object* v___x_2603_; 
lean_dec(v_size_2453_);
v_impl_2602_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2450_, v_v_2451_, v_r_2457_);
v___x_2603_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2456_) == 0)
{
lean_object* v_size_2604_; lean_object* v_size_2605_; lean_object* v_k_2606_; lean_object* v_v_2607_; lean_object* v_l_2608_; lean_object* v_r_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_size_2604_ = lean_ctor_get(v_l_2456_, 0);
v_size_2605_ = lean_ctor_get(v_impl_2602_, 0);
lean_inc(v_size_2605_);
v_k_2606_ = lean_ctor_get(v_impl_2602_, 1);
lean_inc(v_k_2606_);
v_v_2607_ = lean_ctor_get(v_impl_2602_, 2);
lean_inc(v_v_2607_);
v_l_2608_ = lean_ctor_get(v_impl_2602_, 3);
lean_inc(v_l_2608_);
v_r_2609_ = lean_ctor_get(v_impl_2602_, 4);
lean_inc(v_r_2609_);
v___x_2610_ = lean_unsigned_to_nat(3u);
v___x_2611_ = lean_nat_mul(v___x_2610_, v_size_2604_);
v___x_2612_ = lean_nat_dec_lt(v___x_2611_, v_size_2605_);
lean_dec(v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_r_2609_);
lean_dec(v_l_2608_);
lean_dec(v_v_2607_);
lean_dec(v_k_2606_);
v___x_2613_ = lean_nat_add(v___x_2603_, v_size_2604_);
v___x_2614_ = lean_nat_add(v___x_2613_, v_size_2605_);
lean_dec(v_size_2605_);
lean_dec(v___x_2613_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_impl_2602_);
lean_ctor_set(v___x_2459_, 0, v___x_2614_);
v___x_2616_ = v___x_2459_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_l_2456_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_impl_2602_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2681_; 
v_isSharedCheck_2681_ = !lean_is_exclusive(v_impl_2602_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; lean_object* v_unused_2683_; lean_object* v_unused_2684_; lean_object* v_unused_2685_; lean_object* v_unused_2686_; 
v_unused_2682_ = lean_ctor_get(v_impl_2602_, 4);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_impl_2602_, 3);
lean_dec(v_unused_2683_);
v_unused_2684_ = lean_ctor_get(v_impl_2602_, 2);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v_impl_2602_, 1);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_impl_2602_, 0);
lean_dec(v_unused_2686_);
v___x_2619_ = v_impl_2602_;
v_isShared_2620_ = v_isSharedCheck_2681_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v_impl_2602_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2681_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_size_2621_; lean_object* v_k_2622_; lean_object* v_v_2623_; lean_object* v_l_2624_; lean_object* v_r_2625_; lean_object* v_size_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_size_2621_ = lean_ctor_get(v_l_2608_, 0);
v_k_2622_ = lean_ctor_get(v_l_2608_, 1);
v_v_2623_ = lean_ctor_get(v_l_2608_, 2);
v_l_2624_ = lean_ctor_get(v_l_2608_, 3);
v_r_2625_ = lean_ctor_get(v_l_2608_, 4);
v_size_2626_ = lean_ctor_get(v_r_2609_, 0);
v___x_2627_ = lean_unsigned_to_nat(2u);
v___x_2628_ = lean_nat_mul(v___x_2627_, v_size_2626_);
v___x_2629_ = lean_nat_dec_lt(v_size_2621_, v___x_2628_);
lean_dec(v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2657_; 
lean_inc(v_r_2625_);
lean_inc(v_l_2624_);
lean_inc(v_v_2623_);
lean_inc(v_k_2622_);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_l_2608_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; lean_object* v_unused_2662_; 
v_unused_2658_ = lean_ctor_get(v_l_2608_, 4);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_l_2608_, 3);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_l_2608_, 2);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_l_2608_, 1);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_l_2608_, 0);
lean_dec(v_unused_2662_);
v___x_2631_ = v_l_2608_;
v_isShared_2632_ = v_isSharedCheck_2657_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_l_2608_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2657_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2647_; 
v___x_2633_ = lean_nat_add(v___x_2603_, v_size_2604_);
v___x_2634_ = lean_nat_add(v___x_2633_, v_size_2605_);
lean_dec(v_size_2605_);
if (lean_obj_tag(v_l_2624_) == 0)
{
lean_object* v_size_2655_; 
v_size_2655_ = lean_ctor_get(v_l_2624_, 0);
lean_inc(v_size_2655_);
v___y_2647_ = v_size_2655_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___y_2647_ = v___x_2656_;
goto v___jp_2646_;
}
v___jp_2635_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_nat_add(v___y_2636_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec(v___y_2636_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 4, v_r_2609_);
lean_ctor_set(v___x_2631_, 3, v_r_2625_);
lean_ctor_set(v___x_2631_, 2, v_v_2607_);
lean_ctor_set(v___x_2631_, 1, v_k_2606_);
lean_ctor_set(v___x_2631_, 0, v___x_2639_);
v___x_2641_ = v___x_2631_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_k_2606_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_v_2607_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v_r_2625_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v_r_2609_);
v___x_2641_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2643_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___x_2641_);
lean_ctor_set(v___x_2619_, 3, v___y_2637_);
lean_ctor_set(v___x_2619_, 2, v_v_2623_);
lean_ctor_set(v___x_2619_, 1, v_k_2622_);
lean_ctor_set(v___x_2619_, 0, v___x_2634_);
v___x_2643_ = v___x_2619_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_k_2622_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_v_2623_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v___y_2637_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
v___jp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = lean_nat_add(v___x_2633_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec(v___x_2633_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_l_2624_);
lean_ctor_set(v___x_2459_, 0, v___x_2648_);
v___x_2650_ = v___x_2459_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_l_2456_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_l_2624_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_nat_add(v___x_2603_, v_size_2626_);
if (lean_obj_tag(v_r_2625_) == 0)
{
lean_object* v_size_2652_; 
v_size_2652_ = lean_ctor_get(v_r_2625_, 0);
lean_inc(v_size_2652_);
v___y_2636_ = v___x_2651_;
v___y_2637_ = v___x_2650_;
v___y_2638_ = v_size_2652_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___y_2636_ = v___x_2651_;
v___y_2637_ = v___x_2650_;
v___y_2638_ = v___x_2653_;
goto v___jp_2635_;
}
}
}
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_del_object(v___x_2459_);
v___x_2663_ = lean_nat_add(v___x_2603_, v_size_2604_);
v___x_2664_ = lean_nat_add(v___x_2663_, v_size_2605_);
lean_dec(v_size_2605_);
v___x_2665_ = lean_nat_add(v___x_2663_, v_size_2621_);
lean_dec(v___x_2663_);
lean_inc_ref(v_l_2456_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v_l_2608_);
lean_ctor_set(v___x_2619_, 3, v_l_2456_);
lean_ctor_set(v___x_2619_, 2, v_v_2455_);
lean_ctor_set(v___x_2619_, 1, v_k_2454_);
lean_ctor_set(v___x_2619_, 0, v___x_2665_);
v___x_2667_ = v___x_2619_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v_l_2456_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v_l_2608_);
v___x_2667_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_isSharedCheck_2674_ = !lean_is_exclusive(v_l_2456_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; lean_object* v_unused_2678_; lean_object* v_unused_2679_; 
v_unused_2675_ = lean_ctor_get(v_l_2456_, 4);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2456_, 3);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2456_, 2);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_l_2456_, 1);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2456_, 0);
lean_dec(v_unused_2679_);
v___x_2669_ = v_l_2456_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v_l_2456_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 4, v_r_2609_);
lean_ctor_set(v___x_2669_, 3, v___x_2667_);
lean_ctor_set(v___x_2669_, 2, v_v_2607_);
lean_ctor_set(v___x_2669_, 1, v_k_2606_);
lean_ctor_set(v___x_2669_, 0, v___x_2664_);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_k_2606_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_v_2607_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_r_2609_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2687_; 
v_l_2687_ = lean_ctor_get(v_impl_2602_, 3);
lean_inc(v_l_2687_);
if (lean_obj_tag(v_l_2687_) == 0)
{
lean_object* v_r_2688_; lean_object* v_k_2689_; lean_object* v_v_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2713_; 
v_r_2688_ = lean_ctor_get(v_impl_2602_, 4);
v_k_2689_ = lean_ctor_get(v_impl_2602_, 1);
v_v_2690_ = lean_ctor_get(v_impl_2602_, 2);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_impl_2602_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2714_ = lean_ctor_get(v_impl_2602_, 3);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_impl_2602_, 0);
lean_dec(v_unused_2715_);
v___x_2692_ = v_impl_2602_;
v_isShared_2693_ = v_isSharedCheck_2713_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_r_2688_);
lean_inc(v_v_2690_);
lean_inc(v_k_2689_);
lean_dec(v_impl_2602_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2713_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_k_2694_; lean_object* v_v_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2709_; 
v_k_2694_ = lean_ctor_get(v_l_2687_, 1);
v_v_2695_ = lean_ctor_get(v_l_2687_, 2);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_l_2687_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2710_ = lean_ctor_get(v_l_2687_, 4);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_l_2687_, 3);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_l_2687_, 0);
lean_dec(v_unused_2712_);
v___x_2697_ = v_l_2687_;
v_isShared_2698_ = v_isSharedCheck_2709_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_v_2695_);
lean_inc(v_k_2694_);
lean_dec(v_l_2687_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2709_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2688_, 2);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 4, v_r_2688_);
lean_ctor_set(v___x_2697_, 3, v_r_2688_);
lean_ctor_set(v___x_2697_, 2, v_v_2455_);
lean_ctor_set(v___x_2697_, 1, v_k_2454_);
lean_ctor_set(v___x_2697_, 0, v___x_2603_);
v___x_2701_ = v___x_2697_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_r_2688_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_r_2688_);
v___x_2701_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
lean_inc(v_r_2688_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 3, v_r_2688_);
lean_ctor_set(v___x_2692_, 0, v___x_2603_);
v___x_2703_ = v___x_2692_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2690_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_r_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_r_2688_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v___x_2703_);
lean_ctor_set(v___x_2459_, 3, v___x_2701_);
lean_ctor_set(v___x_2459_, 2, v_v_2695_);
lean_ctor_set(v___x_2459_, 1, v_k_2694_);
lean_ctor_set(v___x_2459_, 0, v___x_2699_);
v___x_2705_ = v___x_2459_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_k_2694_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_v_2695_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
else
{
lean_object* v_r_2716_; 
v_r_2716_ = lean_ctor_get(v_impl_2602_, 4);
lean_inc(v_r_2716_);
if (lean_obj_tag(v_r_2716_) == 0)
{
lean_object* v_k_2717_; lean_object* v_v_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2729_; 
v_k_2717_ = lean_ctor_get(v_impl_2602_, 1);
v_v_2718_ = lean_ctor_get(v_impl_2602_, 2);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_impl_2602_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2730_ = lean_ctor_get(v_impl_2602_, 4);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_impl_2602_, 3);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_impl_2602_, 0);
lean_dec(v_unused_2732_);
v___x_2720_ = v_impl_2602_;
v_isShared_2721_ = v_isSharedCheck_2729_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_v_2718_);
lean_inc(v_k_2717_);
lean_dec(v_impl_2602_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2729_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = lean_unsigned_to_nat(3u);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 4, v_l_2687_);
lean_ctor_set(v___x_2720_, 2, v_v_2455_);
lean_ctor_set(v___x_2720_, 1, v_k_2454_);
lean_ctor_set(v___x_2720_, 0, v___x_2603_);
v___x_2724_ = v___x_2720_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_l_2687_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_l_2687_);
v___x_2724_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2726_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_r_2716_);
lean_ctor_set(v___x_2459_, 3, v___x_2724_);
lean_ctor_set(v___x_2459_, 2, v_v_2718_);
lean_ctor_set(v___x_2459_, 1, v_k_2717_);
lean_ctor_set(v___x_2459_, 0, v___x_2722_);
v___x_2726_ = v___x_2459_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_k_2717_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_v_2718_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_r_2716_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_unsigned_to_nat(2u);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 4, v_impl_2602_);
lean_ctor_set(v___x_2459_, 3, v_r_2716_);
lean_ctor_set(v___x_2459_, 0, v___x_2733_);
v___x_2735_ = v___x_2459_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_r_2716_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_impl_2602_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
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
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_k_2450_);
lean_ctor_set(v___x_2739_, 2, v_v_2451_);
lean_ctor_set(v___x_2739_, 3, v_t_2452_);
lean_ctor_set(v___x_2739_, 4, v_t_2452_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_bs_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_bs_2742_);
return v___x_2744_;
}
else
{
lean_object* v_v_2745_; lean_object* v___x_2746_; lean_object* v_bs_x27_2747_; lean_object* v_a_2749_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2820_; 
v_v_2745_ = lean_array_uget(v_bs_2742_, v_i_2741_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v_bs_x27_2747_ = lean_array_uset(v_bs_2742_, v_i_2741_, v___x_2746_);
v___x_2754_ = lean_array_get_size(v_v_2745_);
v___x_2755_ = lean_unsigned_to_nat(4u);
v___x_2820_ = lean_nat_dec_eq(v___x_2754_, v___x_2755_);
if (v___x_2820_ == 0)
{
if (v___x_2743_ == 0)
{
goto v___jp_2756_;
}
else
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_unsigned_to_nat(5u);
v___x_2822_ = lean_nat_dec_eq(v___x_2754_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v_bs_x27_2747_);
lean_dec(v_v_2745_);
v___x_2823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2824_ = l_Nat_reprFast(v___x_2754_);
v___x_2825_ = lean_string_append(v___x_2823_, v___x_2824_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
else
{
goto v___jp_2756_;
}
}
}
else
{
goto v___jp_2756_;
}
v___jp_2748_:
{
size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_add(v_i_2741_, v___x_2750_);
v___x_2752_ = lean_array_uset(v_bs_x27_2747_, v_i_2741_, v_a_2749_);
v_i_2741_ = v___x_2751_;
v_bs_2742_ = v___x_2752_;
goto _start;
}
v___jp_2756_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_array_fget_borrowed(v_v_2745_, v___x_2746_);
lean_inc(v___x_2757_);
v___x_2758_ = l_Lean_Json_getNat_x3f(v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec_ref(v_bs_x27_2747_);
lean_dec(v_v_2745_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_a_2767_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2768_ = lean_unsigned_to_nat(1u);
v___x_2769_ = lean_array_fget_borrowed(v_v_2745_, v___x_2768_);
lean_inc(v___x_2769_);
v___x_2770_ = l_Lean_Json_getNat_x3f(v___x_2769_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2767_);
lean_dec_ref(v_bs_x27_2747_);
lean_dec(v_v_2745_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_a_2779_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2780_ = lean_unsigned_to_nat(2u);
v___x_2781_ = lean_array_fget_borrowed(v_v_2745_, v___x_2780_);
lean_inc(v___x_2781_);
v___x_2782_ = l_Lean_Json_getNat_x3f(v___x_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2779_);
lean_dec(v_a_2767_);
lean_dec_ref(v_bs_x27_2747_);
lean_dec(v_v_2745_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2791_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2792_ = lean_unsigned_to_nat(3u);
v___x_2793_ = lean_array_fget_borrowed(v_v_2745_, v___x_2792_);
lean_inc(v___x_2793_);
v___x_2794_ = l_Lean_Json_getNat_x3f(v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2791_);
lean_dec(v_a_2779_);
lean_dec(v_a_2767_);
lean_dec_ref(v_bs_x27_2747_);
lean_dec(v_v_2745_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_a_2803_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2804_ = lean_unsigned_to_nat(5u);
v___x_2805_ = lean_nat_dec_eq(v___x_2754_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec(v_v_2745_);
v___x_2806_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2767_);
lean_ctor_set(v___x_2807_, 1, v_a_2779_);
lean_ctor_set(v___x_2807_, 2, v_a_2791_);
lean_ctor_set(v___x_2807_, 3, v_a_2803_);
lean_ctor_set(v___x_2807_, 4, v___x_2806_);
v_a_2749_ = v___x_2807_;
goto v___jp_2748_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_array_fget(v_v_2745_, v___x_2755_);
lean_dec(v_v_2745_);
v___x_2809_ = l_Lean_Json_getStr_x3f(v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2791_);
lean_dec(v_a_2779_);
lean_dec(v_a_2767_);
lean_dec_ref(v_bs_x27_2747_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2819_, 0, v_a_2767_);
lean_ctor_set(v___x_2819_, 1, v_a_2779_);
lean_ctor_set(v___x_2819_, 2, v_a_2791_);
lean_ctor_set(v___x_2819_, 3, v_a_2803_);
lean_ctor_set(v___x_2819_, 4, v_a_2818_);
v_a_2749_ = v___x_2819_;
goto v___jp_2748_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2827_, lean_object* v_i_2828_, lean_object* v_bs_2829_){
_start:
{
size_t v_sz_boxed_2830_; size_t v_i_boxed_2831_; lean_object* v_res_2832_; 
v_sz_boxed_2830_ = lean_unbox_usize(v_sz_2827_);
lean_dec(v_sz_2827_);
v_i_boxed_2831_ = lean_unbox_usize(v_i_2828_);
lean_dec(v_i_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2830_, v_i_boxed_2831_, v_bs_2829_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2833_, size_t v_i_2834_, lean_object* v_bs_2835_){
_start:
{
uint8_t v___x_2836_; 
v___x_2836_ = lean_usize_dec_lt(v_i_2834_, v_sz_2833_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; 
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_bs_2835_);
return v___x_2837_;
}
else
{
lean_object* v_v_2838_; lean_object* v___x_2839_; 
v_v_2838_ = lean_array_uget_borrowed(v_bs_2835_, v_i_2834_);
lean_inc(v_v_2838_);
v___x_2839_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_bs_2835_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v_bs_x27_2850_; size_t v___x_2851_; size_t v___x_2852_; lean_object* v___x_2853_; 
v_a_2848_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2849_ = lean_unsigned_to_nat(0u);
v_bs_x27_2850_ = lean_array_uset(v_bs_2835_, v_i_2834_, v___x_2849_);
v___x_2851_ = ((size_t)1ULL);
v___x_2852_ = lean_usize_add(v_i_2834_, v___x_2851_);
v___x_2853_ = lean_array_uset(v_bs_x27_2850_, v_i_2834_, v_a_2848_);
v_i_2834_ = v___x_2852_;
v_bs_2835_ = v___x_2853_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2855_, lean_object* v_i_2856_, lean_object* v_bs_2857_){
_start:
{
size_t v_sz_boxed_2858_; size_t v_i_boxed_2859_; lean_object* v_res_2860_; 
v_sz_boxed_2858_ = lean_unbox_usize(v_sz_2855_);
lean_dec(v_sz_2855_);
v_i_boxed_2859_ = lean_unbox_usize(v_i_2856_);
lean_dec(v_i_2856_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2858_, v_i_boxed_2859_, v_bs_2857_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 4)
{
lean_object* v_elems_2862_; size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
v_elems_2862_ = lean_ctor_get(v_x_2861_, 0);
lean_inc_ref(v_elems_2862_);
lean_dec_ref_known(v_x_2861_, 1);
v_sz_2863_ = lean_array_size(v_elems_2862_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2863_, v___x_2864_, v_elems_2862_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2866_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2867_ = lean_unsigned_to_nat(80u);
v___x_2868_ = l_Lean_Json_pretty(v_x_2861_, v___x_2867_);
v___x_2869_ = lean_string_append(v___x_2866_, v___x_2868_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2873_, lean_object* v_k_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = l_Lean_Json_getObjValD(v_j_2873_, v_k_2874_);
v___x_2876_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2877_, lean_object* v_k_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2877_, v_k_2878_);
lean_dec_ref(v_k_2878_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2880_, lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 0)
{
lean_object* v_k_2882_; lean_object* v_v_2883_; lean_object* v_l_2884_; lean_object* v_r_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3045_; 
v_k_2882_ = lean_ctor_get(v_x_2881_, 1);
v_v_2883_ = lean_ctor_get(v_x_2881_, 2);
v_l_2884_ = lean_ctor_get(v_x_2881_, 3);
v_r_2885_ = lean_ctor_get(v_x_2881_, 4);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_x_2881_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v_x_2881_, 0);
lean_dec(v_unused_3046_);
v___x_2887_ = v_x_2881_;
v_isShared_2888_ = v_isSharedCheck_3045_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_r_2885_);
lean_inc(v_l_2884_);
lean_inc(v_v_2883_);
lean_inc(v_k_2882_);
lean_dec(v_x_2881_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3045_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2880_, v_l_2884_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
lean_dec(v_k_2882_);
return v___x_2889_;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3044_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_3044_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3044_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Json_parse(v_k_2882_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2904_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v_definition_x3f_2915_; lean_object* v_a_2943_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2913_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2947_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2883_);
v___x_2948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2883_, v___x_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3043_; 
v_a_2957_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_2959_ = v___x_2948_;
v_isShared_2960_ = v_isSharedCheck_3043_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2948_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3043_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
if (lean_obj_tag(v_a_2957_) == 0)
{
lean_object* v___x_2961_; 
lean_del_object(v___x_2959_);
lean_del_object(v___x_2892_);
lean_del_object(v___x_2887_);
v___x_2961_ = lean_box(0);
v_definition_x3f_2915_ = v___x_2961_;
goto v___jp_2914_;
}
else
{
lean_object* v_val_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_3034_; 
v_val_2962_ = lean_ctor_get(v_a_2957_, 0);
lean_inc(v_val_2962_);
lean_dec_ref_known(v_a_2957_, 1);
v___x_2963_ = lean_array_get_size(v_val_2962_);
v___x_2964_ = lean_unsigned_to_nat(4u);
v___x_3034_ = lean_nat_dec_eq(v___x_2963_, v___x_2964_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = lean_unsigned_to_nat(5u);
v___x_3036_ = lean_nat_dec_eq(v___x_2963_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_val_2962_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v___x_3037_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3038_ = l_Nat_reprFast(v___x_2963_);
v___x_3039_ = lean_string_append(v___x_3037_, v___x_3038_);
lean_dec_ref(v___x_3038_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
lean_ctor_set(v___x_2959_, 0, v___x_3039_);
v___x_3041_ = v___x_2959_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
else
{
lean_del_object(v___x_2959_);
goto v___jp_2965_;
}
}
else
{
lean_del_object(v___x_2959_);
goto v___jp_2965_;
}
v___jp_2965_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_array_fget_borrowed(v_val_2962_, v___x_2966_);
lean_inc(v___x_2967_);
v___x_2968_ = l_Lean_Json_getNat_x3f(v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_val_2962_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2977_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2978_ = lean_unsigned_to_nat(1u);
v___x_2979_ = lean_array_fget_borrowed(v_val_2962_, v___x_2978_);
lean_inc(v___x_2979_);
v___x_2980_ = l_Lean_Json_getNat_x3f(v___x_2979_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v_a_2977_);
lean_dec(v_val_2962_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2990_ = lean_unsigned_to_nat(2u);
v___x_2991_ = lean_array_fget_borrowed(v_val_2962_, v___x_2990_);
lean_inc(v___x_2991_);
v___x_2992_ = l_Lean_Json_getNat_x3f(v___x_2991_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_a_2989_);
lean_dec(v_a_2977_);
lean_dec(v_val_2962_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3001_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_3002_ = lean_unsigned_to_nat(3u);
v___x_3003_ = lean_array_fget_borrowed(v_val_2962_, v___x_3002_);
lean_inc(v___x_3003_);
v___x_3004_ = l_Lean_Json_getNat_x3f(v___x_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_3001_);
lean_dec(v_a_2989_);
lean_dec(v_a_2977_);
lean_dec(v_val_2962_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3014_ = lean_unsigned_to_nat(5u);
v___x_3015_ = lean_nat_dec_eq(v___x_2963_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
lean_dec(v_val_2962_);
v___x_3016_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 4, v___x_3016_);
lean_ctor_set(v___x_2887_, 3, v_a_3013_);
lean_ctor_set(v___x_2887_, 2, v_a_3001_);
lean_ctor_set(v___x_2887_, 1, v_a_2989_);
lean_ctor_set(v___x_2887_, 0, v_a_2977_);
v___x_3018_ = v___x_2887_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2977_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_a_2989_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_a_3001_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3019_, 4, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
v_a_2943_ = v___x_3018_;
goto v___jp_2942_;
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_array_fget(v_val_2962_, v___x_2964_);
lean_dec(v_val_2962_);
v___x_3021_ = l_Lean_Json_getStr_x3f(v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_3013_);
lean_dec(v_a_3001_);
lean_dec(v_a_2989_);
lean_dec(v_a_2977_);
lean_dec(v_a_2913_);
lean_del_object(v___x_2892_);
lean_dec(v_a_2890_);
lean_del_object(v___x_2887_);
lean_dec(v_r_2885_);
lean_dec(v_v_2883_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
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
lean_object* v_a_3030_; lean_object* v___x_3032_; 
v_a_3030_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3021_, 1);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 4, v_a_3030_);
lean_ctor_set(v___x_2887_, 3, v_a_3013_);
lean_ctor_set(v___x_2887_, 2, v_a_3001_);
lean_ctor_set(v___x_2887_, 1, v_a_2989_);
lean_ctor_set(v___x_2887_, 0, v_a_2977_);
v___x_3032_ = v___x_2887_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_2977_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_a_2989_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_a_3001_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v_a_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
v_a_2943_ = v___x_3032_;
goto v___jp_2942_;
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
v___jp_2914_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2917_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2883_, v___x_2916_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_definition_x3f_2915_);
lean_dec(v_a_2913_);
lean_dec(v_a_2890_);
lean_dec(v_r_2885_);
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2926_; size_t v_sz_2927_; size_t v___x_2928_; lean_object* v___x_2929_; 
v_a_2926_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2917_, 1);
v_sz_2927_ = lean_array_size(v_a_2926_);
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2927_, v___x_2928_, v_a_2926_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_definition_x3f_2915_);
lean_dec(v_a_2913_);
lean_dec(v_a_2890_);
lean_dec(v_r_2885_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_a_2938_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_definition_x3f_2915_);
lean_ctor_set(v___x_2939_, 1, v_a_2938_);
v___x_2940_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2913_, v___x_2939_, v_a_2890_);
v_init_2880_ = v___x_2940_;
v_x_2881_ = v_r_2885_;
goto _start;
}
}
}
v___jp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v_a_2943_);
v___x_2945_ = v___x_2892_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
v_definition_x3f_2915_ = v___x_2945_;
goto v___jp_2914_;
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
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_init_2880_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3048_, lean_object* v_k_3049_){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = l_Lean_Json_getObjValD(v_j_3048_, v_k_3049_);
v___x_3051_ = l_Lean_Json_getObj_x3f(v___x_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3051_, 1);
v___x_3061_ = lean_box(1);
v___x_3062_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3061_, v_a_3060_);
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3063_, lean_object* v_k_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3063_, v_k_3064_);
lean_dec_ref(v_k_3064_);
return v_res_3065_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = 1;
v___x_3072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3073_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3072_, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3076_ = lean_string_append(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3078_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3079_ = lean_string_append(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3082_ = lean_string_append(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = 1;
v___x_3087_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3088_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3090_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3091_ = lean_string_append(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3093_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3094_ = lean_string_append(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = 1;
v___x_3099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3100_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3099_, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3102_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3103_ = lean_string_append(v___x_3102_, v___x_3101_);
return v___x_3103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3106_ = lean_string_append(v___x_3105_, v___x_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3107_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3107_);
v___x_3109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3107_, v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_json_3107_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3119_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3119_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3115_ = lean_string_append(v___x_3114_, v_a_3110_);
lean_dec(v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3115_);
v___x_3117_ = v___x_3112_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_json_3107_);
v_a_3120_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3109_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3109_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 0);
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3128_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3107_);
v___x_3130_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3107_, v___x_3129_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_a_3128_);
lean_dec(v_json_3107_);
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3140_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3136_ = lean_string_append(v___x_3135_, v_a_3131_);
lean_dec(v_a_3131_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3136_);
v___x_3138_ = v___x_3133_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_a_3128_);
lean_dec(v_json_3107_);
v_a_3141_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3130_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3130_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 0);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_a_3149_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3151_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3107_, v___x_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_a_3149_);
lean_dec(v_a_3128_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3161_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3161_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3157_ = lean_string_append(v___x_3156_, v_a_3152_);
lean_dec(v_a_3152_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3157_);
v___x_3159_ = v___x_3154_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_a_3149_);
lean_dec(v_a_3128_);
v_a_3162_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3151_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3151_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 0);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
v_a_3170_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3172_ = v___x_3151_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3151_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v_a_3128_);
lean_ctor_set(v___x_3174_, 1, v_a_3149_);
lean_ctor_set(v___x_3174_, 2, v_a_3170_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3179_, lean_object* v_k_3180_, lean_object* v_v_3181_, lean_object* v_t_3182_, lean_object* v_hl_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3180_, v_v_3181_, v_t_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3185_, lean_object* v_k_3186_, lean_object* v_v_3187_, lean_object* v_t_3188_, lean_object* v_hl_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3186_, v_v_3187_, v_t_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3193_, lean_object* v_x_3194_){
_start:
{
if (lean_obj_tag(v_x_3194_) == 0)
{
lean_object* v_k_3195_; lean_object* v_v_3196_; lean_object* v_l_3197_; lean_object* v_r_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_k_3195_ = lean_ctor_get(v_x_3194_, 1);
v_v_3196_ = lean_ctor_get(v_x_3194_, 2);
v_l_3197_ = lean_ctor_get(v_x_3194_, 3);
v_r_3198_ = lean_ctor_get(v_x_3194_, 4);
v___x_3199_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3193_, v_r_3198_);
lean_inc(v_v_3196_);
lean_inc(v_k_3195_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_k_3195_);
lean_ctor_set(v___x_3200_, 1, v_v_3196_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3199_);
v_init_3193_ = v___x_3201_;
v_x_3194_ = v_l_3197_;
goto _start;
}
else
{
return v_init_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3203_, v_x_3204_);
lean_dec(v_x_3204_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3206_, size_t v_i_3207_, lean_object* v_bs_3208_){
_start:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_usize_dec_lt(v_i_3207_, v_sz_3206_);
if (v___x_3209_ == 0)
{
return v_bs_3208_;
}
else
{
lean_object* v_v_3210_; lean_object* v___x_3211_; lean_object* v_bs_x27_3212_; size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; 
v_v_3210_ = lean_array_uget(v_bs_3208_, v_i_3207_);
v___x_3211_ = lean_unsigned_to_nat(0u);
v_bs_x27_3212_ = lean_array_uset(v_bs_3208_, v_i_3207_, v___x_3211_);
v___x_3213_ = ((size_t)1ULL);
v___x_3214_ = lean_usize_add(v_i_3207_, v___x_3213_);
v___x_3215_ = lean_array_uset(v_bs_x27_3212_, v_i_3207_, v_v_3210_);
v_i_3207_ = v___x_3214_;
v_bs_3208_ = v___x_3215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3217_, lean_object* v_i_3218_, lean_object* v_bs_3219_){
_start:
{
size_t v_sz_boxed_3220_; size_t v_i_boxed_3221_; lean_object* v_res_3222_; 
v_sz_boxed_3220_ = lean_unbox_usize(v_sz_3217_);
lean_dec(v_sz_3217_);
v_i_boxed_3221_ = lean_unbox_usize(v_i_3218_);
lean_dec(v_i_3218_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3220_, v_i_boxed_3221_, v_bs_3219_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3223_){
_start:
{
size_t v_sz_3224_; size_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_sz_3224_ = lean_array_size(v_a_3223_);
v___x_3225_ = ((size_t)0ULL);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3224_, v___x_3225_, v_a_3223_);
v___x_3227_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_array_mk(v_a_3228_);
v___x_3230_ = l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_box(0);
return v___x_3232_;
}
else
{
lean_object* v_val_3233_; lean_object* v___x_3234_; 
v_val_3233_ = lean_ctor_get(v_x_3231_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v_x_3231_, 1);
v___x_3234_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3233_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3235_, size_t v_i_3236_, lean_object* v_bs_3237_){
_start:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_usize_dec_lt(v_i_3236_, v_sz_3235_);
if (v___x_3238_ == 0)
{
return v_bs_3237_;
}
else
{
lean_object* v_v_3239_; lean_object* v___x_3240_; lean_object* v_bs_x27_3241_; lean_object* v___x_3242_; size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v_v_3239_ = lean_array_uget(v_bs_3237_, v_i_3236_);
v___x_3240_ = lean_unsigned_to_nat(0u);
v_bs_x27_3241_ = lean_array_uset(v_bs_3237_, v_i_3236_, v___x_3240_);
v___x_3242_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3239_);
v___x_3243_ = ((size_t)1ULL);
v___x_3244_ = lean_usize_add(v_i_3236_, v___x_3243_);
v___x_3245_ = lean_array_uset(v_bs_x27_3241_, v_i_3236_, v___x_3242_);
v_i_3236_ = v___x_3244_;
v_bs_3237_ = v___x_3245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3247_, lean_object* v_i_3248_, lean_object* v_bs_3249_){
_start:
{
size_t v_sz_boxed_3250_; size_t v_i_boxed_3251_; lean_object* v_res_3252_; 
v_sz_boxed_3250_ = lean_unbox_usize(v_sz_3247_);
lean_dec(v_sz_3247_);
v_i_boxed_3251_ = lean_unbox_usize(v_i_3248_);
lean_dec(v_i_3248_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3250_, v_i_boxed_3251_, v_bs_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3253_){
_start:
{
size_t v_sz_3254_; size_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_sz_3254_ = lean_array_size(v_a_3253_);
v___x_3255_ = ((size_t)0ULL);
v___x_3256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3254_, v___x_3255_, v_a_3253_);
v___x_3257_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
if (lean_obj_tag(v_a_3258_) == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = l_List_reverse___redArg(v_a_3259_);
return v___x_3260_;
}
else
{
lean_object* v_head_3261_; lean_object* v_tail_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3272_; 
v_head_3261_ = lean_ctor_get(v_a_3258_, 0);
v_tail_3262_ = lean_ctor_get(v_a_3258_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_a_3258_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3264_ = v_a_3258_;
v_isShared_3265_ = v_isSharedCheck_3272_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_tail_3262_);
lean_inc(v_head_3261_);
lean_dec(v_a_3258_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3272_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3266_ = l_Lean_JsonNumber_fromNat(v_head_3261_);
v___x_3267_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 1, v_a_3259_);
lean_ctor_set(v___x_3264_, 0, v___x_3267_);
v___x_3269_ = v___x_3264_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3259_);
v___x_3269_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
v_a_3258_ = v_tail_3262_;
v_a_3259_ = v___x_3269_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3273_, size_t v_i_3274_, lean_object* v_bs_3275_){
_start:
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_usize_dec_lt(v_i_3274_, v_sz_3273_);
if (v___x_3276_ == 0)
{
return v_bs_3275_;
}
else
{
lean_object* v_v_3277_; lean_object* v_startPosLine_3278_; lean_object* v_startPosCharacter_3279_; lean_object* v_endPosLine_3280_; lean_object* v_endPosCharacter_3281_; lean_object* v___x_3282_; lean_object* v_bs_x27_3283_; lean_object* v___y_3285_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_range_3295_; lean_object* v___x_3296_; 
v_v_3277_ = lean_array_uget(v_bs_3275_, v_i_3274_);
v_startPosLine_3278_ = lean_ctor_get(v_v_3277_, 0);
v_startPosCharacter_3279_ = lean_ctor_get(v_v_3277_, 1);
v_endPosLine_3280_ = lean_ctor_get(v_v_3277_, 2);
v_endPosCharacter_3281_ = lean_ctor_get(v_v_3277_, 3);
v___x_3282_ = lean_unsigned_to_nat(0u);
v_bs_x27_3283_ = lean_array_uset(v_bs_3275_, v_i_3274_, v___x_3282_);
v___x_3290_ = lean_box(0);
lean_inc(v_endPosCharacter_3281_);
v___x_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_endPosCharacter_3281_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
lean_inc(v_endPosLine_3280_);
v___x_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_endPosLine_3280_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
lean_inc(v_startPosCharacter_3279_);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_startPosCharacter_3279_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
lean_inc(v_startPosLine_3278_);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_startPosLine_3278_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v_range_3295_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3294_, v___x_3290_);
v___x_3296_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3277_);
lean_dec(v_v_3277_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = l_List_appendTR___redArg(v_range_3295_, v___x_3290_);
v___y_3285_ = v___x_3297_;
goto v___jp_3284_;
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3307_; 
v_val_3298_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3300_ = v___x_3296_;
v_isShared_3301_ = v_isSharedCheck_3307_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_val_3298_);
lean_dec(v___x_3296_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3307_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 3);
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3298_);
v___x_3303_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3290_);
v___x_3305_ = l_List_appendTR___redArg(v_range_3295_, v___x_3304_);
v___y_3285_ = v___x_3305_;
goto v___jp_3284_;
}
}
}
v___jp_3284_:
{
size_t v___x_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_add(v_i_3274_, v___x_3286_);
v___x_3288_ = lean_array_uset(v_bs_x27_3283_, v_i_3274_, v___y_3285_);
v_i_3274_ = v___x_3287_;
v_bs_3275_ = v___x_3288_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3308_, lean_object* v_i_3309_, lean_object* v_bs_3310_){
_start:
{
size_t v_sz_boxed_3311_; size_t v_i_boxed_3312_; lean_object* v_res_3313_; 
v_sz_boxed_3311_ = lean_unbox_usize(v_sz_3308_);
lean_dec(v_sz_3308_);
v_i_boxed_3312_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3311_, v_i_boxed_3312_, v_bs_3310_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
if (lean_obj_tag(v_a_3314_) == 0)
{
lean_object* v___x_3316_; 
v___x_3316_ = l_List_reverse___redArg(v_a_3315_);
return v___x_3316_;
}
else
{
lean_object* v_head_3317_; lean_object* v_snd_3318_; lean_object* v_tail_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3388_; 
v_head_3317_ = lean_ctor_get(v_a_3314_, 0);
lean_inc(v_head_3317_);
v_snd_3318_ = lean_ctor_get(v_head_3317_, 1);
lean_inc(v_snd_3318_);
v_tail_3319_ = lean_ctor_get(v_a_3314_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_a_3314_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v_a_3314_, 0);
lean_dec(v_unused_3389_);
v___x_3321_ = v_a_3314_;
v_isShared_3322_ = v_isSharedCheck_3388_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_tail_3319_);
lean_dec(v_a_3314_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3388_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_fst_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3386_; 
v_fst_3323_ = lean_ctor_get(v_head_3317_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_head_3317_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_head_3317_, 1);
lean_dec(v_unused_3387_);
v___x_3325_ = v_head_3317_;
v_isShared_3326_ = v_isSharedCheck_3386_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_fst_3323_);
lean_dec(v_head_3317_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3386_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_definition_x3f_3327_; lean_object* v_usages_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3385_; 
v_definition_x3f_3327_ = lean_ctor_get(v_snd_3318_, 0);
v_usages_3328_ = lean_ctor_get(v_snd_3318_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_snd_3318_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3330_ = v_snd_3318_;
v_isShared_3331_ = v_isSharedCheck_3385_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_usages_3328_);
lean_inc(v_definition_x3f_3327_);
lean_dec(v_snd_3318_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3385_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___y_3336_; lean_object* v___y_3359_; 
v___x_3332_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3323_);
v___x_3333_ = l_Lean_Json_compress(v___x_3332_);
v___x_3334_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3327_) == 0)
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_box(0);
v___y_3336_ = v___x_3361_;
goto v___jp_3335_;
}
else
{
lean_object* v_val_3362_; lean_object* v_startPosLine_3363_; lean_object* v_startPosCharacter_3364_; lean_object* v_endPosLine_3365_; lean_object* v_endPosCharacter_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_range_3372_; lean_object* v___x_3373_; 
v_val_3362_ = lean_ctor_get(v_definition_x3f_3327_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v_definition_x3f_3327_, 1);
v_startPosLine_3363_ = lean_ctor_get(v_val_3362_, 0);
v_startPosCharacter_3364_ = lean_ctor_get(v_val_3362_, 1);
v_endPosLine_3365_ = lean_ctor_get(v_val_3362_, 2);
v_endPosCharacter_3366_ = lean_ctor_get(v_val_3362_, 3);
v___x_3367_ = lean_box(0);
lean_inc(v_endPosCharacter_3366_);
v___x_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_endPosCharacter_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
lean_inc(v_endPosLine_3365_);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v_endPosLine_3365_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
lean_inc(v_startPosCharacter_3364_);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v_startPosCharacter_3364_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
lean_inc(v_startPosLine_3363_);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_startPosLine_3363_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v_range_3372_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3371_, v___x_3367_);
v___x_3373_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3362_);
lean_dec(v_val_3362_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l_List_appendTR___redArg(v_range_3372_, v___x_3367_);
v___y_3359_ = v___x_3374_;
goto v___jp_3358_;
}
else
{
lean_object* v_val_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3384_; 
v_val_3375_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3377_ = v___x_3373_;
v_isShared_3378_ = v_isSharedCheck_3384_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_val_3375_);
lean_dec(v___x_3373_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3384_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set_tag(v___x_3377_, 3);
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_val_3375_);
v___x_3380_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___x_3367_);
v___x_3382_ = l_List_appendTR___redArg(v_range_3372_, v___x_3381_);
v___y_3359_ = v___x_3382_;
goto v___jp_3358_;
}
}
}
}
v___jp_3335_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3336_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v___x_3337_);
lean_ctor_set(v___x_3325_, 0, v___x_3334_);
v___x_3339_ = v___x_3325_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3340_; size_t v_sz_3341_; size_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3340_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3341_ = lean_array_size(v_usages_3328_);
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3341_, v___x_3342_, v_usages_3328_);
v___x_3344_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3343_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3344_);
lean_ctor_set(v___x_3330_, 0, v___x_3340_);
v___x_3346_ = v___x_3330_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_box(0);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 1, v___x_3347_);
lean_ctor_set(v___x_3321_, 0, v___x_3346_);
v___x_3349_ = v___x_3321_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3339_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = l_Lean_Json_mkObj(v___x_3350_);
lean_dec_ref_known(v___x_3350_, 2);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3333_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v_a_3315_);
v_a_3314_ = v_tail_3319_;
v_a_3315_ = v___x_3353_;
goto _start;
}
}
}
}
v___jp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3359_);
v___y_3336_ = v___x_3360_;
goto v___jp_3335_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = l_List_reverse___redArg(v_a_3391_);
return v___x_3392_;
}
else
{
lean_object* v_head_3393_; lean_object* v_snd_3394_; lean_object* v_tail_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3447_; 
v_head_3393_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_head_3393_);
v_snd_3394_ = lean_ctor_get(v_head_3393_, 1);
lean_inc(v_snd_3394_);
v_tail_3395_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v_a_3390_, 0);
lean_dec(v_unused_3448_);
v___x_3397_ = v_a_3390_;
v_isShared_3398_ = v_isSharedCheck_3447_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_tail_3395_);
lean_dec(v_a_3390_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3447_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3445_; 
v_fst_3399_ = lean_ctor_get(v_head_3393_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_head_3393_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v_head_3393_, 1);
lean_dec(v_unused_3446_);
v___x_3401_ = v_head_3393_;
v_isShared_3402_ = v_isSharedCheck_3445_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_fst_3399_);
lean_dec(v_head_3393_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3445_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_rangeStartPosLine_3403_; lean_object* v_rangeStartPosCharacter_3404_; lean_object* v_rangeEndPosLine_3405_; lean_object* v_rangeEndPosCharacter_3406_; lean_object* v_selectionRangeStartPosLine_3407_; lean_object* v_selectionRangeStartPosCharacter_3408_; lean_object* v_selectionRangeEndPosLine_3409_; lean_object* v_selectionRangeEndPosCharacter_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v_rangeStartPosLine_3403_ = lean_ctor_get(v_snd_3394_, 0);
lean_inc(v_rangeStartPosLine_3403_);
v_rangeStartPosCharacter_3404_ = lean_ctor_get(v_snd_3394_, 1);
lean_inc(v_rangeStartPosCharacter_3404_);
v_rangeEndPosLine_3405_ = lean_ctor_get(v_snd_3394_, 2);
lean_inc(v_rangeEndPosLine_3405_);
v_rangeEndPosCharacter_3406_ = lean_ctor_get(v_snd_3394_, 3);
lean_inc(v_rangeEndPosCharacter_3406_);
v_selectionRangeStartPosLine_3407_ = lean_ctor_get(v_snd_3394_, 4);
lean_inc(v_selectionRangeStartPosLine_3407_);
v_selectionRangeStartPosCharacter_3408_ = lean_ctor_get(v_snd_3394_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3408_);
v_selectionRangeEndPosLine_3409_ = lean_ctor_get(v_snd_3394_, 6);
lean_inc(v_selectionRangeEndPosLine_3409_);
v_selectionRangeEndPosCharacter_3410_ = lean_ctor_get(v_snd_3394_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3410_);
lean_dec(v_snd_3394_);
v___x_3411_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3403_);
v___x_3412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
v___x_3413_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3404_);
v___x_3414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
v___x_3415_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3405_);
v___x_3416_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
v___x_3417_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3406_);
v___x_3418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3407_);
v___x_3420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
v___x_3421_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3408_);
v___x_3422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
v___x_3423_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3409_);
v___x_3424_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
v___x_3425_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3410_);
v___x_3426_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
v___x_3427_ = lean_unsigned_to_nat(8u);
v___x_3428_ = lean_mk_empty_array_with_capacity(v___x_3427_);
v___x_3429_ = lean_array_push(v___x_3428_, v___x_3412_);
v___x_3430_ = lean_array_push(v___x_3429_, v___x_3414_);
v___x_3431_ = lean_array_push(v___x_3430_, v___x_3416_);
v___x_3432_ = lean_array_push(v___x_3431_, v___x_3418_);
v___x_3433_ = lean_array_push(v___x_3432_, v___x_3420_);
v___x_3434_ = lean_array_push(v___x_3433_, v___x_3422_);
v___x_3435_ = lean_array_push(v___x_3434_, v___x_3424_);
v___x_3436_ = lean_array_push(v___x_3435_, v___x_3426_);
v___x_3437_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v___x_3437_);
v___x_3439_ = v___x_3401_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_fst_3399_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 1, v_a_3391_);
lean_ctor_set(v___x_3397_, 0, v___x_3439_);
v___x_3441_ = v___x_3397_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_a_3391_);
v___x_3441_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v_a_3390_ = v_tail_3395_;
v_a_3391_ = v___x_3441_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3449_, lean_object* v_x_3450_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_object* v_k_3451_; lean_object* v_v_3452_; lean_object* v_l_3453_; lean_object* v_r_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_k_3451_ = lean_ctor_get(v_x_3450_, 1);
v_v_3452_ = lean_ctor_get(v_x_3450_, 2);
v_l_3453_ = lean_ctor_get(v_x_3450_, 3);
v_r_3454_ = lean_ctor_get(v_x_3450_, 4);
v___x_3455_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3449_, v_r_3454_);
lean_inc(v_v_3452_);
lean_inc(v_k_3451_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_k_3451_);
lean_ctor_set(v___x_3456_, 1, v_v_3452_);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
v_init_3449_ = v___x_3457_;
v_x_3450_ = v_l_3453_;
goto _start;
}
else
{
return v_init_3449_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3459_, lean_object* v_x_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3459_, v_x_3460_);
lean_dec(v_x_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3462_){
_start:
{
lean_object* v_version_3463_; lean_object* v_references_3464_; lean_object* v_decls_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_version_3463_ = lean_ctor_get(v_x_3462_, 0);
lean_inc(v_version_3463_);
v_references_3464_ = lean_ctor_get(v_x_3462_, 1);
lean_inc(v_references_3464_);
v_decls_3465_ = lean_ctor_get(v_x_3462_, 2);
lean_inc(v_decls_3465_);
lean_dec_ref(v_x_3462_);
v___x_3466_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3467_ = l_Lean_JsonNumber_fromNat(v_version_3463_);
v___x_3468_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3466_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3473_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3470_, v_references_3464_);
lean_dec(v_references_3464_);
v___x_3474_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3473_, v___x_3470_);
v___x_3475_ = l_Lean_Json_mkObj(v___x_3474_);
lean_dec(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3472_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3470_);
v___x_3478_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3470_, v_decls_3465_);
lean_dec(v_decls_3465_);
v___x_3480_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3479_, v___x_3470_);
v___x_3481_ = l_Lean_Json_mkObj(v___x_3480_);
lean_dec(v___x_3480_);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3478_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
lean_ctor_set(v___x_3483_, 1, v___x_3470_);
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___x_3470_);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3477_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3471_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3488_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3486_, v___x_3487_);
v___x_3489_ = l_Lean_Json_mkObj(v___x_3488_);
lean_dec(v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3492_, size_t v_i_3493_, lean_object* v_bs_3494_){
_start:
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_usize_dec_lt(v_i_3493_, v_sz_3492_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_bs_3494_);
return v___x_3496_;
}
else
{
lean_object* v_v_3497_; lean_object* v___x_3498_; 
v_v_3497_ = lean_array_uget_borrowed(v_bs_3494_, v_i_3493_);
lean_inc(v_v_3497_);
v___x_3498_ = l_Lean_Json_getStr_x3f(v_v_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v_bs_3494_);
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3508_; lean_object* v_bs_x27_3509_; size_t v___x_3510_; size_t v___x_3511_; lean_object* v___x_3512_; 
v_a_3507_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3498_, 1);
v___x_3508_ = lean_unsigned_to_nat(0u);
v_bs_x27_3509_ = lean_array_uset(v_bs_3494_, v_i_3493_, v___x_3508_);
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3493_, v___x_3510_);
v___x_3512_ = lean_array_uset(v_bs_x27_3509_, v_i_3493_, v_a_3507_);
v_i_3493_ = v___x_3511_;
v_bs_3494_ = v___x_3512_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3514_, lean_object* v_i_3515_, lean_object* v_bs_3516_){
_start:
{
size_t v_sz_boxed_3517_; size_t v_i_boxed_3518_; lean_object* v_res_3519_; 
v_sz_boxed_3517_ = lean_unbox_usize(v_sz_3514_);
lean_dec(v_sz_3514_);
v_i_boxed_3518_ = lean_unbox_usize(v_i_3515_);
lean_dec(v_i_3515_);
v_res_3519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3517_, v_i_boxed_3518_, v_bs_3516_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3520_){
_start:
{
if (lean_obj_tag(v_x_3520_) == 4)
{
lean_object* v_elems_3521_; size_t v_sz_3522_; size_t v___x_3523_; lean_object* v___x_3524_; 
v_elems_3521_ = lean_ctor_get(v_x_3520_, 0);
lean_inc_ref(v_elems_3521_);
lean_dec_ref_known(v_x_3520_, 1);
v_sz_3522_ = lean_array_size(v_elems_3521_);
v___x_3523_ = ((size_t)0ULL);
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3522_, v___x_3523_, v_elems_3521_);
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3525_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3526_ = lean_unsigned_to_nat(80u);
v___x_3527_ = l_Lean_Json_pretty(v_x_3520_, v___x_3526_);
v___x_3528_ = lean_string_append(v___x_3525_, v___x_3527_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3530_ = lean_string_append(v___x_3528_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3532_, lean_object* v_k_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = l_Lean_Json_getObjValD(v_j_3532_, v_k_3533_);
v___x_3535_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3536_, lean_object* v_k_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3536_, v_k_3537_);
lean_dec_ref(v_k_3537_);
return v_res_3538_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = 1;
v___x_3546_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3546_, v___x_3545_);
return v___x_3547_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3549_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3550_ = lean_string_append(v___x_3549_, v___x_3548_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = 1;
v___x_3554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3555_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3554_, v___x_3553_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3557_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3558_ = lean_string_append(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3560_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3561_ = lean_string_append(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3562_){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3564_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3562_, v___x_3563_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3570_ = lean_string_append(v___x_3569_, v_a_3565_);
lean_dec(v_a_3565_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_a_3575_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3564_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3564_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 0);
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3564_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3564_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3593_, size_t v_i_3594_, lean_object* v_bs_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_usize_dec_lt(v_i_3594_, v_sz_3593_);
if (v___x_3596_ == 0)
{
return v_bs_3595_;
}
else
{
lean_object* v_v_3597_; lean_object* v___x_3598_; lean_object* v_bs_x27_3599_; lean_object* v___x_3600_; size_t v___x_3601_; size_t v___x_3602_; lean_object* v___x_3603_; 
v_v_3597_ = lean_array_uget(v_bs_3595_, v_i_3594_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v_bs_x27_3599_ = lean_array_uset(v_bs_3595_, v_i_3594_, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_v_3597_);
v___x_3601_ = ((size_t)1ULL);
v___x_3602_ = lean_usize_add(v_i_3594_, v___x_3601_);
v___x_3603_ = lean_array_uset(v_bs_x27_3599_, v_i_3594_, v___x_3600_);
v_i_3594_ = v___x_3602_;
v_bs_3595_ = v___x_3603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3605_, lean_object* v_i_3606_, lean_object* v_bs_3607_){
_start:
{
size_t v_sz_boxed_3608_; size_t v_i_boxed_3609_; lean_object* v_res_3610_; 
v_sz_boxed_3608_ = lean_unbox_usize(v_sz_3605_);
lean_dec(v_sz_3605_);
v_i_boxed_3609_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_res_3610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3608_, v_i_boxed_3609_, v_bs_3607_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3611_){
_start:
{
size_t v_sz_3612_; size_t v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_sz_3612_ = lean_array_size(v_a_3611_);
v___x_3613_ = ((size_t)0ULL);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3612_, v___x_3613_, v_a_3611_);
v___x_3615_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3616_){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3617_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3618_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3616_);
v___x_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_box(0);
v___x_3621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v___x_3620_);
v___x_3623_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3624_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3622_, v___x_3623_);
v___x_3625_ = l_Lean_Json_mkObj(v___x_3624_);
lean_dec(v___x_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3628_, lean_object* v_k_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = l_Lean_Json_getObjValD(v_j_3628_, v_k_3629_);
v___x_3631_ = l_Lean_Json_getStr_x3f(v___x_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3632_, lean_object* v_k_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3632_, v_k_3633_);
lean_dec_ref(v_k_3633_);
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = 1;
v___x_3642_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3642_, v___x_3641_);
return v___x_3643_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3645_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3646_ = lean_string_append(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = 1;
v___x_3650_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3651_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3650_, v___x_3649_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3653_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3654_ = lean_string_append(v___x_3653_, v___x_3652_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3656_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3657_ = lean_string_append(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3658_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3660_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3658_, v___x_3659_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3670_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3670_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3670_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3666_ = lean_string_append(v___x_3665_, v_a_3661_);
lean_dec(v_a_3661_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3666_);
v___x_3668_ = v___x_3663_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
else
{
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
v_a_3671_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3660_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3660_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 0);
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_a_3679_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3660_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3660_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_x_3689_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
lean_ctor_set(v___x_3695_, 1, v___x_3693_);
v___x_3696_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3697_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3695_, v___x_3696_);
v___x_3698_ = l_Lean_Json_mkObj(v___x_3697_);
lean_dec(v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3701_){
_start:
{
if (lean_obj_tag(v_x_3701_) == 0)
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_unsigned_to_nat(0u);
return v___x_3702_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_unsigned_to_nat(1u);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3704_);
lean_dec_ref(v_x_3704_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3706_, lean_object* v_k_3707_){
_start:
{
if (lean_obj_tag(v_t_3706_) == 0)
{
lean_object* v_namespace_3708_; lean_object* v_exceptions_3709_; lean_object* v___x_3710_; 
v_namespace_3708_ = lean_ctor_get(v_t_3706_, 0);
lean_inc(v_namespace_3708_);
v_exceptions_3709_ = lean_ctor_get(v_t_3706_, 1);
lean_inc_ref(v_exceptions_3709_);
lean_dec_ref_known(v_t_3706_, 2);
v___x_3710_ = lean_apply_2(v_k_3707_, v_namespace_3708_, v_exceptions_3709_);
return v___x_3710_;
}
else
{
lean_object* v_from_3711_; lean_object* v_to_3712_; lean_object* v___x_3713_; 
v_from_3711_ = lean_ctor_get(v_t_3706_, 0);
lean_inc(v_from_3711_);
v_to_3712_ = lean_ctor_get(v_t_3706_, 1);
lean_inc(v_to_3712_);
lean_dec_ref_known(v_t_3706_, 2);
v___x_3713_ = lean_apply_2(v_k_3707_, v_from_3711_, v_to_3712_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3714_, lean_object* v_ctorIdx_3715_, lean_object* v_t_3716_, lean_object* v_h_3717_, lean_object* v_k_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3716_, v_k_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3720_, lean_object* v_ctorIdx_3721_, lean_object* v_t_3722_, lean_object* v_h_3723_, lean_object* v_k_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3720_, v_ctorIdx_3721_, v_t_3722_, v_h_3723_, v_k_3724_);
lean_dec(v_ctorIdx_3721_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3726_, lean_object* v_allExcept_3727_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3726_, v_allExcept_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3729_, lean_object* v_t_3730_, lean_object* v_h_3731_, lean_object* v_allExcept_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3730_, v_allExcept_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3734_, lean_object* v_renamed_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3734_, v_renamed_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3737_, lean_object* v_t_3738_, lean_object* v_h_3739_, lean_object* v_renamed_3740_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3738_, v_renamed_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_bs_3744_){
_start:
{
uint8_t v___x_3745_; 
v___x_3745_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_bs_3744_);
return v___x_3746_;
}
else
{
lean_object* v_v_3747_; lean_object* v___x_3748_; 
v_v_3747_ = lean_array_uget_borrowed(v_bs_3744_, v_i_3743_);
lean_inc(v_v_3747_);
v___x_3748_ = l_Lean_Name_fromJson_x3f(v_v_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v_bs_3744_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3748_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3748_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v_bs_x27_3759_; size_t v___x_3760_; size_t v___x_3761_; lean_object* v___x_3762_; 
v_a_3757_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3758_ = lean_unsigned_to_nat(0u);
v_bs_x27_3759_ = lean_array_uset(v_bs_3744_, v_i_3743_, v___x_3758_);
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3743_, v___x_3760_);
v___x_3762_ = lean_array_uset(v_bs_x27_3759_, v_i_3743_, v_a_3757_);
v_i_3743_ = v___x_3761_;
v_bs_3744_ = v___x_3762_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3764_, lean_object* v_i_3765_, lean_object* v_bs_3766_){
_start:
{
size_t v_sz_boxed_3767_; size_t v_i_boxed_3768_; lean_object* v_res_3769_; 
v_sz_boxed_3767_ = lean_unbox_usize(v_sz_3764_);
lean_dec(v_sz_3764_);
v_i_boxed_3768_ = lean_unbox_usize(v_i_3765_);
lean_dec(v_i_3765_);
v_res_3769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3767_, v_i_boxed_3768_, v_bs_3766_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3770_){
_start:
{
if (lean_obj_tag(v_x_3770_) == 4)
{
lean_object* v_elems_3771_; size_t v_sz_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v_elems_3771_ = lean_ctor_get(v_x_3770_, 0);
lean_inc_ref(v_elems_3771_);
lean_dec_ref_known(v_x_3770_, 1);
v_sz_3772_ = lean_array_size(v_elems_3771_);
v___x_3773_ = ((size_t)0ULL);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3772_, v___x_3773_, v_elems_3771_);
return v___x_3774_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3775_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3776_ = lean_unsigned_to_nat(80u);
v___x_3777_ = l_Lean_Json_pretty(v_x_3770_, v___x_3776_);
v___x_3778_ = lean_string_append(v___x_3775_, v___x_3777_);
lean_dec_ref(v___x_3777_);
v___x_3779_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
return v___x_3781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3816_){
_start:
{
lean_object* v___x_3817_; 
lean_inc(v_json_3816_);
v___x_3817_ = l_Lean_Json_getTag_x3f(v_json_3816_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v___x_3818_; 
lean_dec(v_json_3816_);
v___x_3818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3818_;
}
else
{
lean_object* v_val_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v_val_3819_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_val_3819_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3820_ = lean_box(0);
v___x_3821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3822_ = lean_string_dec_eq(v_val_3819_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3824_ = lean_string_dec_eq(v_val_3819_, v___x_3823_);
lean_dec(v_val_3819_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec(v_json_3816_);
v___x_3825_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3825_;
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3826_ = lean_unsigned_to_nat(2u);
v___x_3827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3828_ = l_Lean_Json_parseCtorFields(v_json_3816_, v___x_3823_, v___x_3826_, v___x_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_a_3837_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3828_, 1);
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_array_get_borrowed(v___x_3820_, v_a_3837_, v___x_3838_);
lean_inc(v___x_3839_);
v___x_3840_ = l_Lean_Name_fromJson_x3f(v___x_3839_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v_a_3837_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3849_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_array_get(v___x_3820_, v_a_3837_, v___x_3850_);
lean_dec(v_a_3837_);
v___x_3852_ = l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3851_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_a_3849_);
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3869_; 
v_a_3861_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3863_ = v___x_3852_;
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3852_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_a_3849_);
lean_ctor_set(v___x_3865_, 1, v_a_3861_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec(v_val_3819_);
v___x_3870_ = lean_unsigned_to_nat(2u);
v___x_3871_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3872_ = l_Lean_Json_parseCtorFields(v_json_3816_, v___x_3821_, v___x_3870_, v___x_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_a_3881_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3872_, 1);
v___x_3882_ = lean_unsigned_to_nat(0u);
v___x_3883_ = lean_array_get_borrowed(v___x_3820_, v_a_3881_, v___x_3882_);
lean_inc(v___x_3883_);
v___x_3884_ = l_Lean_Name_fromJson_x3f(v___x_3883_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec(v_a_3881_);
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_a_3893_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_array_get(v___x_3820_, v_a_3881_, v___x_3894_);
lean_dec(v_a_3881_);
v___x_3896_ = l_Lean_Name_fromJson_x3f(v___x_3895_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_a_3893_);
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3913_; 
v_a_3905_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3907_ = v___x_3896_;
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3896_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3913_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v_a_3893_);
lean_ctor_set(v___x_3909_, 1, v_a_3905_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3909_);
v___x_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3916_, size_t v_i_3917_, lean_object* v_bs_3918_){
_start:
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_usize_dec_lt(v_i_3917_, v_sz_3916_);
if (v___x_3919_ == 0)
{
return v_bs_3918_;
}
else
{
lean_object* v_v_3920_; lean_object* v___x_3921_; lean_object* v_bs_x27_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v_v_3920_ = lean_array_uget(v_bs_3918_, v_i_3917_);
v___x_3921_ = lean_unsigned_to_nat(0u);
v_bs_x27_3922_ = lean_array_uset(v_bs_3918_, v_i_3917_, v___x_3921_);
v___x_3923_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3920_, v___x_3919_);
v___x_3924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3917_, v___x_3925_);
v___x_3927_ = lean_array_uset(v_bs_x27_3922_, v_i_3917_, v___x_3924_);
v_i_3917_ = v___x_3926_;
v_bs_3918_ = v___x_3927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3929_, lean_object* v_i_3930_, lean_object* v_bs_3931_){
_start:
{
size_t v_sz_boxed_3932_; size_t v_i_boxed_3933_; lean_object* v_res_3934_; 
v_sz_boxed_3932_ = lean_unbox_usize(v_sz_3929_);
lean_dec(v_sz_3929_);
v_i_boxed_3933_ = lean_unbox_usize(v_i_3930_);
lean_dec(v_i_3930_);
v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3932_, v_i_boxed_3933_, v_bs_3931_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3935_){
_start:
{
size_t v_sz_3936_; size_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_sz_3936_ = lean_array_size(v_a_3935_);
v___x_3937_ = ((size_t)0ULL);
v___x_3938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3936_, v___x_3937_, v_a_3935_);
v___x_3939_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3940_){
_start:
{
if (lean_obj_tag(v_x_3940_) == 0)
{
lean_object* v_namespace_3941_; lean_object* v_exceptions_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3964_; 
v_namespace_3941_ = lean_ctor_get(v_x_3940_, 0);
v_exceptions_3942_ = lean_ctor_get(v_x_3940_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_x_3940_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3944_ = v_x_3940_;
v_isShared_3945_ = v_isSharedCheck_3964_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_exceptions_3942_);
lean_inc(v_namespace_3941_);
lean_dec(v_x_3940_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3964_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3947_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3948_ = 1;
v___x_3949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3941_, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 1, v___x_3950_);
lean_ctor_set(v___x_3944_, 0, v___x_3947_);
v___x_3952_ = v___x_3944_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3953_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3954_ = l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3942_);
v___x_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = lean_box(0);
v___x_3957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3952_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = l_Lean_Json_mkObj(v___x_3958_);
lean_dec_ref_known(v___x_3958_, 2);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3946_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v___x_3956_);
v___x_3962_ = l_Lean_Json_mkObj(v___x_3961_);
lean_dec_ref_known(v___x_3961_, 2);
return v___x_3962_;
}
}
}
else
{
lean_object* v_from_3965_; lean_object* v_to_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3989_; 
v_from_3965_ = lean_ctor_get(v_x_3940_, 0);
v_to_3966_ = lean_ctor_get(v_x_3940_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_x_3940_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3968_ = v_x_3940_;
v_isShared_3969_ = v_isSharedCheck_3989_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_to_3966_);
lean_inc(v_from_3965_);
lean_dec(v_x_3940_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3989_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3970_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3971_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3972_ = 1;
v___x_3973_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3965_, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set_tag(v___x_3968_, 0);
lean_ctor_set(v___x_3968_, 1, v___x_3974_);
lean_ctor_set(v___x_3968_, 0, v___x_3971_);
v___x_3976_ = v___x_3968_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3977_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3978_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3966_, v___x_3972_);
v___x_3979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3977_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = lean_box(0);
v___x_3982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3976_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = l_Lean_Json_mkObj(v___x_3983_);
lean_dec_ref_known(v___x_3983_, 2);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3970_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v___x_3981_);
v___x_3987_ = l_Lean_Json_mkObj(v___x_3986_);
lean_dec_ref_known(v___x_3986_, 2);
return v___x_3987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3992_, size_t v_i_3993_, lean_object* v_bs_3994_){
_start:
{
uint8_t v___x_3995_; 
v___x_3995_ = lean_usize_dec_lt(v_i_3993_, v_sz_3992_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v_bs_3994_);
return v___x_3996_;
}
else
{
lean_object* v_v_3997_; lean_object* v___x_3998_; 
v_v_3997_ = lean_array_uget_borrowed(v_bs_3994_, v_i_3993_);
lean_inc(v_v_3997_);
v___x_3998_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_3997_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec_ref(v_bs_3994_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4008_; lean_object* v_bs_x27_4009_; size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v_a_4007_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4008_ = lean_unsigned_to_nat(0u);
v_bs_x27_4009_ = lean_array_uset(v_bs_3994_, v_i_3993_, v___x_4008_);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_3993_, v___x_4010_);
v___x_4012_ = lean_array_uset(v_bs_x27_4009_, v_i_3993_, v_a_4007_);
v_i_3993_ = v___x_4011_;
v_bs_3994_ = v___x_4012_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4014_, lean_object* v_i_4015_, lean_object* v_bs_4016_){
_start:
{
size_t v_sz_boxed_4017_; size_t v_i_boxed_4018_; lean_object* v_res_4019_; 
v_sz_boxed_4017_ = lean_unbox_usize(v_sz_4014_);
lean_dec(v_sz_4014_);
v_i_boxed_4018_ = lean_unbox_usize(v_i_4015_);
lean_dec(v_i_4015_);
v_res_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4017_, v_i_boxed_4018_, v_bs_4016_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4020_){
_start:
{
if (lean_obj_tag(v_x_4020_) == 4)
{
lean_object* v_elems_4021_; size_t v_sz_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v_elems_4021_ = lean_ctor_get(v_x_4020_, 0);
lean_inc_ref(v_elems_4021_);
lean_dec_ref_known(v_x_4020_, 1);
v_sz_4022_ = lean_array_size(v_elems_4021_);
v___x_4023_ = ((size_t)0ULL);
v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4022_, v___x_4023_, v_elems_4021_);
return v___x_4024_;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4025_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4026_ = lean_unsigned_to_nat(80u);
v___x_4027_ = l_Lean_Json_pretty(v_x_4020_, v___x_4026_);
v___x_4028_ = lean_string_append(v___x_4025_, v___x_4027_);
lean_dec_ref(v___x_4027_);
v___x_4029_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4030_ = lean_string_append(v___x_4028_, v___x_4029_);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4032_, lean_object* v_k_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = l_Lean_Json_getObjValD(v_j_4032_, v_k_4033_);
v___x_4035_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4036_, lean_object* v_k_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4036_, v_k_4037_);
lean_dec_ref(v_k_4037_);
return v_res_4038_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = 1;
v___x_4046_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4046_, v___x_4045_);
return v___x_4047_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4049_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4050_ = lean_string_append(v___x_4049_, v___x_4048_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = 1;
v___x_4054_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4054_, v___x_4053_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4057_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4058_ = lean_string_append(v___x_4057_, v___x_4056_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4060_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4061_ = lean_string_append(v___x_4060_, v___x_4059_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = 1;
v___x_4066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4066_, v___x_4065_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4070_ = lean_string_append(v___x_4069_, v___x_4068_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4072_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4073_ = lean_string_append(v___x_4072_, v___x_4071_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4074_){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4074_);
v___x_4076_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4074_, v___x_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_json_4074_);
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
v___x_4081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
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
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_json_4074_);
v_a_4087_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4076_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4076_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
lean_ctor_set_tag(v___x_4089_, 0);
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_a_4095_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4076_, 1);
v___x_4096_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4097_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4074_, v___x_4096_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_4095_);
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
v___x_4102_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4103_ = lean_string_append(v___x_4102_, v_a_4098_);
lean_dec(v_a_4098_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4103_);
v___x_4105_ = v___x_4100_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
else
{
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_a_4095_);
v_a_4108_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4097_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4097_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set_tag(v___x_4110_, 0);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4124_; 
v_a_4116_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4118_ = v___x_4097_;
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4097_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v_a_4095_);
lean_ctor_set(v___x_4120_, 1, v_a_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4120_);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4127_, size_t v_i_4128_, lean_object* v_bs_4129_){
_start:
{
uint8_t v___x_4130_; 
v___x_4130_ = lean_usize_dec_lt(v_i_4128_, v_sz_4127_);
if (v___x_4130_ == 0)
{
return v_bs_4129_;
}
else
{
lean_object* v_v_4131_; lean_object* v___x_4132_; lean_object* v_bs_x27_4133_; lean_object* v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; lean_object* v___x_4137_; 
v_v_4131_ = lean_array_uget(v_bs_4129_, v_i_4128_);
v___x_4132_ = lean_unsigned_to_nat(0u);
v_bs_x27_4133_ = lean_array_uset(v_bs_4129_, v_i_4128_, v___x_4132_);
v___x_4134_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4131_);
v___x_4135_ = ((size_t)1ULL);
v___x_4136_ = lean_usize_add(v_i_4128_, v___x_4135_);
v___x_4137_ = lean_array_uset(v_bs_x27_4133_, v_i_4128_, v___x_4134_);
v_i_4128_ = v___x_4136_;
v_bs_4129_ = v___x_4137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4139_, lean_object* v_i_4140_, lean_object* v_bs_4141_){
_start:
{
size_t v_sz_boxed_4142_; size_t v_i_boxed_4143_; lean_object* v_res_4144_; 
v_sz_boxed_4142_ = lean_unbox_usize(v_sz_4139_);
lean_dec(v_sz_4139_);
v_i_boxed_4143_ = lean_unbox_usize(v_i_4140_);
lean_dec(v_i_4140_);
v_res_4144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4142_, v_i_boxed_4143_, v_bs_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4145_){
_start:
{
size_t v_sz_4146_; size_t v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_sz_4146_ = lean_array_size(v_a_4145_);
v___x_4147_ = ((size_t)0ULL);
v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4146_, v___x_4147_, v_a_4145_);
v___x_4149_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4150_){
_start:
{
lean_object* v_identifier_4151_; lean_object* v_openNamespaces_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4172_; 
v_identifier_4151_ = lean_ctor_get(v_x_4150_, 0);
v_openNamespaces_4152_ = lean_ctor_get(v_x_4150_, 1);
v_isSharedCheck_4172_ = !lean_is_exclusive(v_x_4150_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4154_ = v_x_4150_;
v_isShared_4155_ = v_isSharedCheck_4172_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_openNamespaces_4152_);
lean_inc(v_identifier_4151_);
lean_dec(v_x_4150_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4172_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_identifier_4151_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 1, v___x_4157_);
lean_ctor_set(v___x_4154_, 0, v___x_4156_);
v___x_4159_ = v___x_4154_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4156_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4160_ = lean_box(0);
v___x_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4163_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4152_);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set(v___x_4165_, 1, v___x_4160_);
v___x_4166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v___x_4160_);
v___x_4167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4161_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4169_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4167_, v___x_4168_);
v___x_4170_ = l_Lean_Json_mkObj(v___x_4169_);
lean_dec(v___x_4169_);
return v___x_4170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4178_, lean_object* v_k_4179_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_Json_getObjValD(v_j_4178_, v_k_4179_);
switch(lean_obj_tag(v___x_4180_))
{
case 3:
{
lean_object* v_s_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4189_; 
v_s_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_s_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4189_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set_tag(v___x_4183_, 0);
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_s_4181_);
v___x_4186_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
}
}
case 2:
{
lean_object* v_n_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4198_; 
v_n_4190_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4192_ = v___x_4180_;
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_n_4190_);
lean_dec(v___x_4180_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 1);
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_n_4190_);
v___x_4195_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
return v___x_4196_;
}
}
}
default: 
{
lean_object* v___x_4199_; 
lean_dec(v___x_4180_);
v___x_4199_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4200_, lean_object* v_k_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4200_, v_k_4201_);
lean_dec_ref(v_k_4201_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4203_, size_t v_i_4204_, lean_object* v_bs_4205_){
_start:
{
uint8_t v___x_4206_; 
v___x_4206_ = lean_usize_dec_lt(v_i_4204_, v_sz_4203_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_bs_4205_);
return v___x_4207_;
}
else
{
lean_object* v_v_4208_; lean_object* v___x_4209_; 
v_v_4208_ = lean_array_uget_borrowed(v_bs_4205_, v_i_4204_);
lean_inc(v_v_4208_);
v___x_4209_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4208_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec_ref(v_bs_4205_);
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4219_; lean_object* v_bs_x27_4220_; size_t v___x_4221_; size_t v___x_4222_; lean_object* v___x_4223_; 
v_a_4218_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4209_, 1);
v___x_4219_ = lean_unsigned_to_nat(0u);
v_bs_x27_4220_ = lean_array_uset(v_bs_4205_, v_i_4204_, v___x_4219_);
v___x_4221_ = ((size_t)1ULL);
v___x_4222_ = lean_usize_add(v_i_4204_, v___x_4221_);
v___x_4223_ = lean_array_uset(v_bs_x27_4220_, v_i_4204_, v_a_4218_);
v_i_4204_ = v___x_4222_;
v_bs_4205_ = v___x_4223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4225_, lean_object* v_i_4226_, lean_object* v_bs_4227_){
_start:
{
size_t v_sz_boxed_4228_; size_t v_i_boxed_4229_; lean_object* v_res_4230_; 
v_sz_boxed_4228_ = lean_unbox_usize(v_sz_4225_);
lean_dec(v_sz_4225_);
v_i_boxed_4229_ = lean_unbox_usize(v_i_4226_);
lean_dec(v_i_4226_);
v_res_4230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4228_, v_i_boxed_4229_, v_bs_4227_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4231_){
_start:
{
if (lean_obj_tag(v_x_4231_) == 4)
{
lean_object* v_elems_4232_; size_t v_sz_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
v_elems_4232_ = lean_ctor_get(v_x_4231_, 0);
lean_inc_ref(v_elems_4232_);
lean_dec_ref_known(v_x_4231_, 1);
v_sz_4233_ = lean_array_size(v_elems_4232_);
v___x_4234_ = ((size_t)0ULL);
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4233_, v___x_4234_, v_elems_4232_);
return v___x_4235_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4236_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4237_ = lean_unsigned_to_nat(80u);
v___x_4238_ = l_Lean_Json_pretty(v_x_4231_, v___x_4237_);
v___x_4239_ = lean_string_append(v___x_4236_, v___x_4238_);
lean_dec_ref(v___x_4238_);
v___x_4240_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4241_ = lean_string_append(v___x_4239_, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4243_, lean_object* v_k_4244_){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = l_Lean_Json_getObjValD(v_j_4243_, v_k_4244_);
v___x_4246_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4247_, lean_object* v_k_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4247_, v_k_4248_);
lean_dec_ref(v_k_4248_);
return v_res_4249_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = 1;
v___x_4257_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4257_, v___x_4256_);
return v___x_4258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4260_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4261_ = lean_string_append(v___x_4260_, v___x_4259_);
return v___x_4261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = 1;
v___x_4265_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4265_, v___x_4264_);
return v___x_4266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4269_ = lean_string_append(v___x_4268_, v___x_4267_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4271_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4272_ = lean_string_append(v___x_4271_, v___x_4270_);
return v___x_4272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = 1;
v___x_4277_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4278_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4277_, v___x_4276_);
return v___x_4278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4281_ = lean_string_append(v___x_4280_, v___x_4279_);
return v___x_4281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4284_ = lean_string_append(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4285_){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4285_);
v___x_4287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4285_, v___x_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
lean_dec(v_json_4285_);
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4292_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4293_ = lean_string_append(v___x_4292_, v_a_4288_);
lean_dec(v_a_4288_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
else
{
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec(v_json_4285_);
v_a_4298_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4287_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4287_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set_tag(v___x_4300_, 0);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_a_4306_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4287_, 1);
v___x_4307_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4285_, v___x_4307_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v_a_4306_);
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4318_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4318_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4313_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4314_ = lean_string_append(v___x_4313_, v_a_4309_);
lean_dec(v_a_4309_);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v___x_4314_);
v___x_4316_ = v___x_4311_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
else
{
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec(v_a_4306_);
v_a_4319_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4308_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4308_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 0);
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4335_; 
v_a_4327_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4329_ = v___x_4308_;
v_isShared_4330_ = v_isSharedCheck_4335_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4308_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4335_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_a_4306_);
lean_ctor_set(v___x_4331_, 1, v_a_4327_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4331_);
v___x_4333_ = v___x_4329_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4338_, size_t v_i_4339_, lean_object* v_bs_4340_){
_start:
{
uint8_t v___x_4341_; 
v___x_4341_ = lean_usize_dec_lt(v_i_4339_, v_sz_4338_);
if (v___x_4341_ == 0)
{
return v_bs_4340_;
}
else
{
lean_object* v_v_4342_; lean_object* v___x_4343_; lean_object* v_bs_x27_4344_; lean_object* v___x_4345_; size_t v___x_4346_; size_t v___x_4347_; lean_object* v___x_4348_; 
v_v_4342_ = lean_array_uget(v_bs_4340_, v_i_4339_);
v___x_4343_ = lean_unsigned_to_nat(0u);
v_bs_x27_4344_ = lean_array_uset(v_bs_4340_, v_i_4339_, v___x_4343_);
v___x_4345_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4342_);
v___x_4346_ = ((size_t)1ULL);
v___x_4347_ = lean_usize_add(v_i_4339_, v___x_4346_);
v___x_4348_ = lean_array_uset(v_bs_x27_4344_, v_i_4339_, v___x_4345_);
v_i_4339_ = v___x_4347_;
v_bs_4340_ = v___x_4348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4350_, lean_object* v_i_4351_, lean_object* v_bs_4352_){
_start:
{
size_t v_sz_boxed_4353_; size_t v_i_boxed_4354_; lean_object* v_res_4355_; 
v_sz_boxed_4353_ = lean_unbox_usize(v_sz_4350_);
lean_dec(v_sz_4350_);
v_i_boxed_4354_ = lean_unbox_usize(v_i_4351_);
lean_dec(v_i_4351_);
v_res_4355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4353_, v_i_boxed_4354_, v_bs_4352_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4356_){
_start:
{
size_t v_sz_4357_; size_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_sz_4357_ = lean_array_size(v_a_4356_);
v___x_4358_ = ((size_t)0ULL);
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4357_, v___x_4358_, v_a_4356_);
v___x_4360_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4361_){
_start:
{
lean_object* v_sourceRequestID_4362_; lean_object* v_queries_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4401_; 
v_sourceRequestID_4362_ = lean_ctor_get(v_x_4361_, 0);
v_queries_4363_ = lean_ctor_get(v_x_4361_, 1);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_x_4361_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4365_ = v_x_4361_;
v_isShared_4366_ = v_isSharedCheck_4401_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_queries_4363_);
lean_inc(v_sourceRequestID_4362_);
lean_dec(v_x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4401_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___y_4369_; 
v___x_4367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4362_))
{
case 0:
{
lean_object* v_s_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_s_4384_ = lean_ctor_get(v_sourceRequestID_4362_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v_sourceRequestID_4362_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v_sourceRequestID_4362_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_s_4384_);
lean_dec(v_sourceRequestID_4362_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 3);
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_s_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
v___y_4369_ = v___x_4389_;
goto v___jp_4368_;
}
}
}
case 1:
{
lean_object* v_n_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_n_4392_ = lean_ctor_get(v_sourceRequestID_4362_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_sourceRequestID_4362_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v_sourceRequestID_4362_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_n_4392_);
lean_dec(v_sourceRequestID_4362_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set_tag(v___x_4394_, 2);
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_n_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
v___y_4369_ = v___x_4397_;
goto v___jp_4368_;
}
}
}
default: 
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_box(0);
v___y_4369_ = v___x_4400_;
goto v___jp_4368_;
}
}
v___jp_4368_:
{
lean_object* v___x_4371_; 
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 1, v___y_4369_);
lean_ctor_set(v___x_4365_, 0, v___x_4367_);
v___x_4371_ = v___x_4365_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___y_4369_);
v___x_4371_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4372_ = lean_box(0);
v___x_4373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4375_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4363_);
v___x_4376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___x_4372_);
v___x_4378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
lean_ctor_set(v___x_4378_, 1, v___x_4372_);
v___x_4379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4373_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4381_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4379_, v___x_4380_);
v___x_4382_ = l_Lean_Json_mkObj(v___x_4381_);
lean_dec(v___x_4381_);
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4404_, lean_object* v_k_4405_){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = l_Lean_Json_getObjValD(v_j_4404_, v_k_4405_);
v___x_4407_ = l_Lean_Name_fromJson_x3f(v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4408_, lean_object* v_k_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4408_, v_k_4409_);
lean_dec_ref(v_k_4409_);
return v_res_4410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = 1;
v___x_4418_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4419_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4422_ = lean_string_append(v___x_4421_, v___x_4420_);
return v___x_4422_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4425_ = 1;
v___x_4426_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4427_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4426_, v___x_4425_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4429_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4430_ = lean_string_append(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4432_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4433_ = lean_string_append(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = 1;
v___x_4438_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4439_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4438_, v___x_4437_);
return v___x_4439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4441_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4442_ = lean_string_append(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4445_ = lean_string_append(v___x_4444_, v___x_4443_);
return v___x_4445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = 1;
v___x_4450_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4451_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4450_, v___x_4449_);
return v___x_4451_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4453_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4454_ = lean_string_append(v___x_4453_, v___x_4452_);
return v___x_4454_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4456_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4457_ = lean_string_append(v___x_4456_, v___x_4455_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4458_){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4458_);
v___x_4460_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4458_, v___x_4459_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_json_4458_);
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4470_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4468_; 
v___x_4465_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4466_ = lean_string_append(v___x_4465_, v_a_4461_);
lean_dec(v_a_4461_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4466_);
v___x_4468_ = v___x_4463_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
else
{
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_json_4458_);
v_a_4471_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4460_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4460_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 0);
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_a_4479_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4460_, 1);
v___x_4480_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4458_);
v___x_4481_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4458_, v___x_4480_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4491_; 
lean_dec(v_a_4479_);
lean_dec(v_json_4458_);
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4486_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4487_ = lean_string_append(v___x_4486_, v_a_4482_);
lean_dec(v_a_4482_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4487_);
v___x_4489_ = v___x_4484_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
else
{
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_a_4479_);
lean_dec(v_json_4458_);
v_a_4492_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4481_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4481_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 0);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v_a_4500_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4501_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4458_, v___x_4501_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4512_; 
lean_dec(v_a_4500_);
lean_dec(v_a_4479_);
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4505_ = v___x_4502_;
v_isShared_4506_ = v_isSharedCheck_4512_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4502_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4512_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4508_ = lean_string_append(v___x_4507_, v_a_4503_);
lean_dec(v_a_4503_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 0, v___x_4508_);
v___x_4510_ = v___x_4505_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
else
{
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v_a_4500_);
lean_dec(v_a_4479_);
v_a_4513_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4502_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4502_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
lean_ctor_set_tag(v___x_4515_, 0);
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4530_; 
v_a_4521_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4523_ = v___x_4502_;
v_isShared_4524_ = v_isSharedCheck_4530_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4502_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4530_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4528_; 
v___x_4525_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4525_, 0, v_a_4479_);
lean_ctor_set(v___x_4525_, 1, v_a_4500_);
v___x_4526_ = lean_unbox(v_a_4521_);
lean_dec(v_a_4521_);
lean_ctor_set_uint8(v___x_4525_, sizeof(void*)*2, v___x_4526_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4525_);
v___x_4528_ = v___x_4523_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4525_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4533_){
_start:
{
lean_object* v_module_4534_; lean_object* v_decl_4535_; uint8_t v_isExactMatch_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v_module_4534_ = lean_ctor_get(v_x_4533_, 0);
lean_inc(v_module_4534_);
v_decl_4535_ = lean_ctor_get(v_x_4533_, 1);
lean_inc(v_decl_4535_);
v_isExactMatch_4536_ = lean_ctor_get_uint8(v_x_4533_, sizeof(void*)*2);
lean_dec_ref(v_x_4533_);
v___x_4537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4538_ = 1;
v___x_4539_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4534_, v___x_4538_);
v___x_4540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
v___x_4541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4537_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = lean_box(0);
v___x_4543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
v___x_4544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4535_, v___x_4538_);
v___x_4546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
v___x_4547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4544_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
lean_ctor_set(v___x_4548_, 1, v___x_4542_);
v___x_4549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4550_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4550_, 0, v_isExactMatch_4536_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
lean_ctor_set(v___x_4552_, 1, v___x_4542_);
v___x_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v___x_4542_);
v___x_4554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4548_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4543_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4557_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4555_, v___x_4556_);
v___x_4558_ = l_Lean_Json_mkObj(v___x_4557_);
lean_dec(v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4561_, size_t v_i_4562_, lean_object* v_bs_4563_){
_start:
{
uint8_t v___x_4564_; 
v___x_4564_ = lean_usize_dec_lt(v_i_4562_, v_sz_4561_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4565_, 0, v_bs_4563_);
return v___x_4565_;
}
else
{
lean_object* v_v_4566_; lean_object* v___x_4567_; 
v_v_4566_ = lean_array_uget_borrowed(v_bs_4563_, v_i_4562_);
lean_inc(v_v_4566_);
v___x_4567_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4566_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref(v_bs_4563_);
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4577_; lean_object* v_bs_x27_4578_; size_t v___x_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v_a_4576_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___x_4567_, 1);
v___x_4577_ = lean_unsigned_to_nat(0u);
v_bs_x27_4578_ = lean_array_uset(v_bs_4563_, v_i_4562_, v___x_4577_);
v___x_4579_ = ((size_t)1ULL);
v___x_4580_ = lean_usize_add(v_i_4562_, v___x_4579_);
v___x_4581_ = lean_array_uset(v_bs_x27_4578_, v_i_4562_, v_a_4576_);
v_i_4562_ = v___x_4580_;
v_bs_4563_ = v___x_4581_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4583_, lean_object* v_i_4584_, lean_object* v_bs_4585_){
_start:
{
size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4583_);
lean_dec(v_sz_4583_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4584_);
lean_dec(v_i_4584_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4586_, v_i_boxed_4587_, v_bs_4585_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4589_){
_start:
{
if (lean_obj_tag(v_x_4589_) == 4)
{
lean_object* v_elems_4590_; size_t v_sz_4591_; size_t v___x_4592_; lean_object* v___x_4593_; 
v_elems_4590_ = lean_ctor_get(v_x_4589_, 0);
lean_inc_ref(v_elems_4590_);
lean_dec_ref_known(v_x_4589_, 1);
v_sz_4591_ = lean_array_size(v_elems_4590_);
v___x_4592_ = ((size_t)0ULL);
v___x_4593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4591_, v___x_4592_, v_elems_4590_);
return v___x_4593_;
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4594_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4595_ = lean_unsigned_to_nat(80u);
v___x_4596_ = l_Lean_Json_pretty(v_x_4589_, v___x_4595_);
v___x_4597_ = lean_string_append(v___x_4594_, v___x_4596_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4599_ = lean_string_append(v___x_4597_, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
return v___x_4600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4601_, size_t v_i_4602_, lean_object* v_bs_4603_){
_start:
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_usize_dec_lt(v_i_4602_, v_sz_4601_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4605_, 0, v_bs_4603_);
return v___x_4605_;
}
else
{
lean_object* v_v_4606_; lean_object* v___x_4607_; 
v_v_4606_ = lean_array_uget_borrowed(v_bs_4603_, v_i_4602_);
lean_inc(v_v_4606_);
v___x_4607_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4606_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec_ref(v_bs_4603_);
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4617_; lean_object* v_bs_x27_4618_; size_t v___x_4619_; size_t v___x_4620_; lean_object* v___x_4621_; 
v_a_4616_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v___x_4607_, 1);
v___x_4617_ = lean_unsigned_to_nat(0u);
v_bs_x27_4618_ = lean_array_uset(v_bs_4603_, v_i_4602_, v___x_4617_);
v___x_4619_ = ((size_t)1ULL);
v___x_4620_ = lean_usize_add(v_i_4602_, v___x_4619_);
v___x_4621_ = lean_array_uset(v_bs_x27_4618_, v_i_4602_, v_a_4616_);
v_i_4602_ = v___x_4620_;
v_bs_4603_ = v___x_4621_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4623_, lean_object* v_i_4624_, lean_object* v_bs_4625_){
_start:
{
size_t v_sz_boxed_4626_; size_t v_i_boxed_4627_; lean_object* v_res_4628_; 
v_sz_boxed_4626_ = lean_unbox_usize(v_sz_4623_);
lean_dec(v_sz_4623_);
v_i_boxed_4627_ = lean_unbox_usize(v_i_4624_);
lean_dec(v_i_4624_);
v_res_4628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4626_, v_i_boxed_4627_, v_bs_4625_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4629_){
_start:
{
if (lean_obj_tag(v_x_4629_) == 4)
{
lean_object* v_elems_4630_; size_t v_sz_4631_; size_t v___x_4632_; lean_object* v___x_4633_; 
v_elems_4630_ = lean_ctor_get(v_x_4629_, 0);
lean_inc_ref(v_elems_4630_);
lean_dec_ref_known(v_x_4629_, 1);
v_sz_4631_ = lean_array_size(v_elems_4630_);
v___x_4632_ = ((size_t)0ULL);
v___x_4633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4631_, v___x_4632_, v_elems_4630_);
return v___x_4633_;
}
else
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4634_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4635_ = lean_unsigned_to_nat(80u);
v___x_4636_ = l_Lean_Json_pretty(v_x_4629_, v___x_4635_);
v___x_4637_ = lean_string_append(v___x_4634_, v___x_4636_);
lean_dec_ref(v___x_4636_);
v___x_4638_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4639_ = lean_string_append(v___x_4637_, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4641_, lean_object* v_k_4642_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = l_Lean_Json_getObjValD(v_j_4641_, v_k_4642_);
v___x_4644_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4645_, lean_object* v_k_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4645_, v_k_4646_);
lean_dec_ref(v_k_4646_);
return v_res_4647_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = 1;
v___x_4655_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4656_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4655_, v___x_4654_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4658_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4659_ = lean_string_append(v___x_4658_, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = 1;
v___x_4663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4663_, v___x_4662_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4667_ = lean_string_append(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4670_ = lean_string_append(v___x_4669_, v___x_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4671_){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4673_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4671_, v___x_4672_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4683_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4679_ = lean_string_append(v___x_4678_, v_a_4674_);
lean_dec(v_a_4674_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v___x_4679_);
v___x_4681_ = v___x_4676_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
else
{
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4673_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4673_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 0);
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
v_a_4692_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4673_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4673_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4702_, size_t v_i_4703_, lean_object* v_bs_4704_){
_start:
{
uint8_t v___x_4705_; 
v___x_4705_ = lean_usize_dec_lt(v_i_4703_, v_sz_4702_);
if (v___x_4705_ == 0)
{
return v_bs_4704_;
}
else
{
lean_object* v_v_4706_; lean_object* v___x_4707_; lean_object* v_bs_x27_4708_; lean_object* v___x_4709_; size_t v___x_4710_; size_t v___x_4711_; lean_object* v___x_4712_; 
v_v_4706_ = lean_array_uget(v_bs_4704_, v_i_4703_);
v___x_4707_ = lean_unsigned_to_nat(0u);
v_bs_x27_4708_ = lean_array_uset(v_bs_4704_, v_i_4703_, v___x_4707_);
v___x_4709_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4706_);
v___x_4710_ = ((size_t)1ULL);
v___x_4711_ = lean_usize_add(v_i_4703_, v___x_4710_);
v___x_4712_ = lean_array_uset(v_bs_x27_4708_, v_i_4703_, v___x_4709_);
v_i_4703_ = v___x_4711_;
v_bs_4704_ = v___x_4712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4714_, lean_object* v_i_4715_, lean_object* v_bs_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4714_);
lean_dec(v_sz_4714_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4715_);
lean_dec(v_i_4715_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4717_, v_i_boxed_4718_, v_bs_4716_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4720_){
_start:
{
size_t v_sz_4721_; size_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v_sz_4721_ = lean_array_size(v_a_4720_);
v___x_4722_ = ((size_t)0ULL);
v___x_4723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4721_, v___x_4722_, v_a_4720_);
v___x_4724_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4725_, size_t v_i_4726_, lean_object* v_bs_4727_){
_start:
{
uint8_t v___x_4728_; 
v___x_4728_ = lean_usize_dec_lt(v_i_4726_, v_sz_4725_);
if (v___x_4728_ == 0)
{
return v_bs_4727_;
}
else
{
lean_object* v_v_4729_; lean_object* v___x_4730_; lean_object* v_bs_x27_4731_; lean_object* v___x_4732_; size_t v___x_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
v_v_4729_ = lean_array_uget(v_bs_4727_, v_i_4726_);
v___x_4730_ = lean_unsigned_to_nat(0u);
v_bs_x27_4731_ = lean_array_uset(v_bs_4727_, v_i_4726_, v___x_4730_);
v___x_4732_ = l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4729_);
v___x_4733_ = ((size_t)1ULL);
v___x_4734_ = lean_usize_add(v_i_4726_, v___x_4733_);
v___x_4735_ = lean_array_uset(v_bs_x27_4731_, v_i_4726_, v___x_4732_);
v_i_4726_ = v___x_4734_;
v_bs_4727_ = v___x_4735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4737_, lean_object* v_i_4738_, lean_object* v_bs_4739_){
_start:
{
size_t v_sz_boxed_4740_; size_t v_i_boxed_4741_; lean_object* v_res_4742_; 
v_sz_boxed_4740_ = lean_unbox_usize(v_sz_4737_);
lean_dec(v_sz_4737_);
v_i_boxed_4741_ = lean_unbox_usize(v_i_4738_);
lean_dec(v_i_4738_);
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4740_, v_i_boxed_4741_, v_bs_4739_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4743_){
_start:
{
size_t v_sz_4744_; size_t v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_sz_4744_ = lean_array_size(v_a_4743_);
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4744_, v___x_4745_, v_a_4743_);
v___x_4747_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4746_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4748_){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4749_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4750_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4748_);
v___x_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = lean_box(0);
v___x_4753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4751_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
lean_ctor_set(v___x_4754_, 1, v___x_4752_);
v___x_4755_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4756_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4754_, v___x_4755_);
v___x_4757_ = l_Lean_Json_mkObj(v___x_4756_);
lean_dec(v___x_4756_);
return v___x_4757_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4769_ = 1;
v___x_4770_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4770_, v___x_4769_);
return v___x_4771_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4772_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4774_ = lean_string_append(v___x_4773_, v___x_4772_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4775_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4777_ = lean_string_append(v___x_4776_, v___x_4775_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4778_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4779_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4780_ = lean_string_append(v___x_4779_, v___x_4778_);
return v___x_4780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4782_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4783_ = lean_string_append(v___x_4782_, v___x_4781_);
return v___x_4783_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4784_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4785_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4786_ = lean_string_append(v___x_4785_, v___x_4784_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4787_){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4787_);
v___x_4789_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4787_, v___x_4788_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_json_4787_);
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4799_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4799_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
v___x_4794_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4795_ = lean_string_append(v___x_4794_, v_a_4790_);
lean_dec(v_a_4790_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4795_);
v___x_4797_ = v___x_4792_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
else
{
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_json_4787_);
v_a_4800_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4789_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4789_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set_tag(v___x_4802_, 0);
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
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
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v_a_4808_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v___x_4789_, 1);
v___x_4809_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4810_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4787_, v___x_4809_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4820_; 
lean_dec(v_a_4808_);
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4820_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4820_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4815_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4816_ = lean_string_append(v___x_4815_, v_a_4811_);
lean_dec(v_a_4811_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4816_);
v___x_4818_ = v___x_4813_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
else
{
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec(v_a_4808_);
v_a_4821_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4810_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4810_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
lean_ctor_set_tag(v___x_4823_, 0);
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4837_; 
v_a_4829_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4831_ = v___x_4810_;
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4810_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4837_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4833_, 0, v_a_4808_);
lean_ctor_set(v___x_4833_, 1, v_a_4829_);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 0, v___x_4833_);
v___x_4835_ = v___x_4831_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4840_){
_start:
{
lean_object* v_module_4841_; lean_object* v_decl_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4865_; 
v_module_4841_ = lean_ctor_get(v_x_4840_, 0);
v_decl_4842_ = lean_ctor_get(v_x_4840_, 1);
v_isSharedCheck_4865_ = !lean_is_exclusive(v_x_4840_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4844_ = v_x_4840_;
v_isShared_4845_ = v_isSharedCheck_4865_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_decl_4842_);
lean_inc(v_module_4841_);
lean_dec(v_x_4840_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4865_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4851_; 
v___x_4846_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4847_ = 1;
v___x_4848_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4841_, v___x_4847_);
v___x_4849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4849_);
lean_ctor_set(v___x_4844_, 0, v___x_4846_);
v___x_4851_ = v___x_4844_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4846_);
lean_ctor_set(v_reuseFailAlloc_4864_, 1, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4852_ = lean_box(0);
v___x_4853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4851_);
lean_ctor_set(v___x_4853_, 1, v___x_4852_);
v___x_4854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4855_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4842_, v___x_4847_);
v___x_4856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
v___x_4857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4854_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
lean_ctor_set(v___x_4858_, 1, v___x_4852_);
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
lean_ctor_set(v___x_4859_, 1, v___x_4852_);
v___x_4860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4853_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4862_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4860_, v___x_4861_);
v___x_4863_ = l_Lean_Json_mkObj(v___x_4862_);
lean_dec(v___x_4862_);
return v___x_4863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4868_, lean_object* v_k_4869_){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = l_Lean_Json_getObjValD(v_j_4868_, v_k_4869_);
v___x_4871_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4872_, lean_object* v_k_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4872_, v_k_4873_);
lean_dec_ref(v_k_4873_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4877_){
_start:
{
if (lean_obj_tag(v_x_4877_) == 0)
{
lean_object* v___x_4878_; 
v___x_4878_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4877_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4896_; 
v_a_4888_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4890_ = v___x_4879_;
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4879_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_a_4888_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4892_);
v___x_4894_ = v___x_4890_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4897_, lean_object* v_k_4898_){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = l_Lean_Json_getObjValD(v_j_4897_, v_k_4898_);
v___x_4900_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4899_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4901_, lean_object* v_k_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4901_, v_k_4902_);
lean_dec_ref(v_k_4902_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4906_){
_start:
{
if (lean_obj_tag(v_x_4906_) == 0)
{
lean_object* v___x_4907_; 
v___x_4907_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4907_;
}
else
{
lean_object* v___x_4908_; 
v___x_4908_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4906_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4925_; 
v_a_4917_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4919_ = v___x_4908_;
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4908_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4925_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_a_4917_);
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v___x_4921_);
v___x_4923_ = v___x_4919_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4926_, lean_object* v_k_4927_){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = l_Lean_Json_getObjValD(v_j_4926_, v_k_4927_);
v___x_4929_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4930_, lean_object* v_k_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4930_, v_k_4931_);
lean_dec_ref(v_k_4931_);
return v_res_4932_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4939_ = 1;
v___x_4940_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4940_, v___x_4939_);
return v___x_4941_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4942_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4944_ = lean_string_append(v___x_4943_, v___x_4942_);
return v___x_4944_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = 1;
v___x_4949_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4950_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4949_, v___x_4948_);
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4952_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4953_ = lean_string_append(v___x_4952_, v___x_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4954_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4955_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4956_ = lean_string_append(v___x_4955_, v___x_4954_);
return v___x_4956_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = 1;
v___x_4961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4962_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4961_, v___x_4960_);
return v___x_4962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4965_ = lean_string_append(v___x_4964_, v___x_4963_);
return v___x_4965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4968_ = lean_string_append(v___x_4967_, v___x_4966_);
return v___x_4968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = 1;
v___x_4973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4973_, v___x_4972_);
return v___x_4974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4977_ = lean_string_append(v___x_4976_, v___x_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4980_ = lean_string_append(v___x_4979_, v___x_4978_);
return v___x_4980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4984_ = 1;
v___x_4985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4985_, v___x_4984_);
return v___x_4986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4989_ = lean_string_append(v___x_4988_, v___x_4987_);
return v___x_4989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4992_ = lean_string_append(v___x_4991_, v___x_4990_);
return v___x_4992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = 1;
v___x_4998_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_4999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4998_, v___x_4997_);
return v___x_4999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_5001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5002_ = lean_string_append(v___x_5001_, v___x_5000_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5003_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5004_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5005_ = lean_string_append(v___x_5004_, v___x_5003_);
return v___x_5005_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = 1;
v___x_5010_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5010_, v___x_5009_);
return v___x_5011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5012_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5014_ = lean_string_append(v___x_5013_, v___x_5012_);
return v___x_5014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5015_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5016_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5017_ = lean_string_append(v___x_5016_, v___x_5015_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5018_){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5018_);
v___x_5020_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5018_, v___x_5019_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5030_; 
lean_dec(v_json_5018_);
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5023_ = v___x_5020_;
v_isShared_5024_ = v_isSharedCheck_5030_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5020_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5030_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5026_ = lean_string_append(v___x_5025_, v_a_5021_);
lean_dec(v_a_5021_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 0, v___x_5026_);
v___x_5028_ = v___x_5023_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
else
{
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_dec(v_json_5018_);
v_a_5031_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5020_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5020_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set_tag(v___x_5033_, 0);
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v_a_5039_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5039_);
lean_dec_ref_known(v___x_5020_, 1);
v___x_5040_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5018_);
v___x_5041_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5018_, v___x_5040_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5051_; 
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5051_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5051_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5049_; 
v___x_5046_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5047_ = lean_string_append(v___x_5046_, v_a_5042_);
lean_dec(v_a_5042_);
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5047_);
v___x_5049_ = v___x_5044_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5047_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
else
{
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5052_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_5041_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5041_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
lean_ctor_set_tag(v___x_5054_, 0);
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_a_5060_ = lean_ctor_get(v___x_5041_, 0);
lean_inc(v_a_5060_);
lean_dec_ref_known(v___x_5041_, 1);
v___x_5061_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5018_);
v___x_5062_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5018_, v___x_5061_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5072_; 
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5065_ = v___x_5062_;
v_isShared_5066_ = v_isSharedCheck_5072_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5072_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5067_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5068_ = lean_string_append(v___x_5067_, v_a_5063_);
lean_dec(v_a_5063_);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5068_);
v___x_5070_ = v___x_5065_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
else
{
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5073_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5062_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5062_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
lean_ctor_set_tag(v___x_5075_, 0);
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v_a_5081_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5081_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5082_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5018_);
v___x_5083_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5018_, v___x_5082_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5093_; 
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5086_ = v___x_5083_;
v_isShared_5087_ = v_isSharedCheck_5093_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5083_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5093_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5088_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5089_ = lean_string_append(v___x_5088_, v_a_5084_);
lean_dec(v_a_5084_);
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 0, v___x_5089_);
v___x_5091_ = v___x_5086_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
else
{
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5094_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5083_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5083_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set_tag(v___x_5096_, 0);
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
else
{
lean_object* v_a_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v_a_5102_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5083_, 1);
v___x_5103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5018_);
v___x_5104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5018_, v___x_5103_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_a_5102_);
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5114_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5114_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5110_ = lean_string_append(v___x_5109_, v_a_5105_);
lean_dec(v_a_5105_);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5110_);
v___x_5112_ = v___x_5107_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
else
{
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
lean_dec(v_a_5102_);
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
lean_dec(v_json_5018_);
v_a_5115_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5104_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5104_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 0);
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
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
lean_object* v_a_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
v_a_5123_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5104_, 1);
v___x_5124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5125_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5018_, v___x_5124_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5135_; 
lean_dec(v_a_5123_);
lean_dec(v_a_5102_);
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5135_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5135_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; 
v___x_5130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5131_ = lean_string_append(v___x_5130_, v_a_5126_);
lean_dec(v_a_5126_);
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5131_);
v___x_5133_ = v___x_5128_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5131_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
else
{
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_dec(v_a_5123_);
lean_dec(v_a_5102_);
lean_dec(v_a_5081_);
lean_dec(v_a_5060_);
lean_dec(v_a_5039_);
v_a_5136_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5125_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5125_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
lean_ctor_set_tag(v___x_5138_, 0);
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5154_; 
v_a_5144_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5146_ = v___x_5125_;
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5125_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5154_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; lean_object* v___x_5152_; 
v___x_5148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5148_, 0, v_a_5039_);
lean_ctor_set(v___x_5148_, 1, v_a_5060_);
lean_ctor_set(v___x_5148_, 2, v_a_5081_);
lean_ctor_set(v___x_5148_, 3, v_a_5102_);
v___x_5149_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5149_, 0, v___x_5148_);
lean_ctor_set(v___x_5149_, 1, v_a_5123_);
v___x_5150_ = lean_unbox(v_a_5144_);
lean_dec(v_a_5144_);
lean_ctor_set_uint8(v___x_5149_, sizeof(void*)*2, v___x_5150_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5149_);
v___x_5152_ = v___x_5146_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5149_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5157_, lean_object* v_x_5158_){
_start:
{
if (lean_obj_tag(v_x_5158_) == 0)
{
lean_object* v___x_5159_; 
lean_dec_ref(v_k_5157_);
v___x_5159_ = lean_box(0);
return v___x_5159_;
}
else
{
lean_object* v_val_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v_val_5160_ = lean_ctor_get(v_x_5158_, 0);
lean_inc(v_val_5160_);
lean_dec_ref_known(v_x_5158_, 1);
v___x_5161_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5160_);
v___x_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5162_, 0, v_k_5157_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
v___x_5163_ = lean_box(0);
v___x_5164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5162_);
lean_ctor_set(v___x_5164_, 1, v___x_5163_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5165_, lean_object* v_x_5166_){
_start:
{
if (lean_obj_tag(v_x_5166_) == 0)
{
lean_object* v___x_5167_; 
lean_dec_ref(v_k_5165_);
v___x_5167_ = lean_box(0);
return v___x_5167_;
}
else
{
lean_object* v_val_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_val_5168_ = lean_ctor_get(v_x_5166_, 0);
lean_inc(v_val_5168_);
lean_dec_ref_known(v_x_5166_, 1);
v___x_5169_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5168_);
v___x_5170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5170_, 0, v_k_5165_);
lean_ctor_set(v___x_5170_, 1, v___x_5169_);
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5170_);
lean_ctor_set(v___x_5172_, 1, v___x_5171_);
return v___x_5172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5173_){
_start:
{
lean_object* v_toLocationLink_5174_; lean_object* v_ident_x3f_5175_; uint8_t v_isDefault_5176_; lean_object* v_originSelectionRange_x3f_5177_; lean_object* v_targetUri_5178_; lean_object* v_targetRange_5179_; lean_object* v_targetSelectionRange_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v_toLocationLink_5174_ = lean_ctor_get(v_x_5173_, 0);
lean_inc_ref(v_toLocationLink_5174_);
v_ident_x3f_5175_ = lean_ctor_get(v_x_5173_, 1);
lean_inc(v_ident_x3f_5175_);
v_isDefault_5176_ = lean_ctor_get_uint8(v_x_5173_, sizeof(void*)*2);
lean_dec_ref(v_x_5173_);
v_originSelectionRange_x3f_5177_ = lean_ctor_get(v_toLocationLink_5174_, 0);
lean_inc(v_originSelectionRange_x3f_5177_);
v_targetUri_5178_ = lean_ctor_get(v_toLocationLink_5174_, 1);
lean_inc_ref(v_targetUri_5178_);
v_targetRange_5179_ = lean_ctor_get(v_toLocationLink_5174_, 2);
lean_inc_ref(v_targetRange_5179_);
v_targetSelectionRange_5180_ = lean_ctor_get(v_toLocationLink_5174_, 3);
lean_inc_ref(v_targetSelectionRange_5180_);
lean_dec_ref(v_toLocationLink_5174_);
v___x_5181_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5182_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5181_, v_originSelectionRange_x3f_5177_);
v___x_5183_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5184_, 0, v_targetUri_5178_);
v___x_5185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5183_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
v___x_5186_ = lean_box(0);
v___x_5187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5185_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5189_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5179_);
v___x_5190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5188_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5190_);
lean_ctor_set(v___x_5191_, 1, v___x_5186_);
v___x_5192_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5193_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5180_);
v___x_5194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5192_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
v___x_5195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5194_);
lean_ctor_set(v___x_5195_, 1, v___x_5186_);
v___x_5196_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5197_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5196_, v_ident_x3f_5175_);
v___x_5198_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5199_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5199_, 0, v_isDefault_5176_);
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5198_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
lean_ctor_set(v___x_5201_, 1, v___x_5186_);
v___x_5202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
lean_ctor_set(v___x_5202_, 1, v___x_5186_);
v___x_5203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5197_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5195_);
lean_ctor_set(v___x_5204_, 1, v___x_5203_);
v___x_5205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5191_);
lean_ctor_set(v___x_5205_, 1, v___x_5204_);
v___x_5206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5187_);
lean_ctor_set(v___x_5206_, 1, v___x_5205_);
v___x_5207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5182_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5209_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5207_, v___x_5208_);
v___x_5210_ = l_Lean_Json_mkObj(v___x_5209_);
lean_dec(v___x_5209_);
return v___x_5210_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Internal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

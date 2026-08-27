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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonImportInfo___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object*);
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
v___x_1112_ = l_Lean_Option_toJson___redArg(v___x_1100_, v___y_1111_);
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
v___x_1120_ = l_Lean_Array_toJson___redArg(v___x_1100_, v___x_1119_);
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
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___y_1156_; uint8_t v___y_1235_; uint8_t v___y_1236_; uint8_t v___y_1237_; uint8_t v___y_1243_; uint8_t v___x_1248_; 
v___x_1153_ = lean_array_get_size(v_a_1152_);
v___x_1154_ = lean_unsigned_to_nat(4u);
v___x_1248_ = lean_nat_dec_eq(v___x_1153_, v___x_1154_);
if (v___x_1248_ == 0)
{
uint8_t v___x_1249_; 
v___x_1249_ = 1;
v___y_1243_ = v___x_1249_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
v___y_1243_ = v___x_1250_;
goto v___jp_1242_;
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_array_fget_borrowed(v_a_1152_, v___x_1157_);
lean_inc(v___x_1158_);
v___x_1159_ = l_Lean_Json_getNat_x3f(v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
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
lean_dec_ref_known(v___x_1159_, 1);
v___x_1169_ = lean_unsigned_to_nat(1u);
v___x_1170_ = lean_array_fget_borrowed(v_a_1152_, v___x_1169_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_Json_getNat_x3f(v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1168_);
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
lean_dec_ref_known(v___x_1171_, 1);
v___x_1181_ = lean_unsigned_to_nat(2u);
v___x_1182_ = lean_array_fget_borrowed(v_a_1152_, v___x_1181_);
lean_inc(v___x_1182_);
v___x_1183_ = l_Lean_Json_getNat_x3f(v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
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
lean_dec_ref_known(v___x_1183_, 1);
v___x_1193_ = lean_unsigned_to_nat(3u);
v___x_1194_ = lean_array_fget_borrowed(v_a_1152_, v___x_1193_);
lean_inc(v___x_1194_);
v___x_1195_ = l_Lean_Json_getNat_x3f(v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_a_1192_);
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
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
if (v___y_1156_ == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v_a_1204_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1206_ = v___x_1195_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1195_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1208_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1209_, 0, v_a_1168_);
lean_ctor_set(v___x_1209_, 1, v_a_1180_);
lean_ctor_set(v___x_1209_, 2, v_a_1192_);
lean_ctor_set(v___x_1209_, 3, v_a_1204_);
lean_ctor_set(v___x_1209_, 4, v___x_1208_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
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
lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_a_1214_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1215_ = lean_array_fget_borrowed(v_a_1152_, v___x_1154_);
lean_inc(v___x_1215_);
v___x_1216_ = l_Lean_Json_getStr_x3f(v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1214_);
lean_dec(v_a_1192_);
lean_dec(v_a_1180_);
lean_dec(v_a_1168_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
v_a_1225_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1227_ = v___x_1216_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1216_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1168_);
lean_ctor_set(v___x_1229_, 1, v_a_1180_);
lean_ctor_set(v___x_1229_, 2, v_a_1192_);
lean_ctor_set(v___x_1229_, 3, v_a_1214_);
lean_ctor_set(v___x_1229_, 4, v_a_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
}
}
v___jp_1234_:
{
if (v___y_1236_ == 0)
{
v___y_1156_ = v___y_1235_;
goto v___jp_1155_;
}
else
{
if (v___y_1237_ == 0)
{
v___y_1156_ = v___y_1235_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1239_ = l_Nat_reprFast(v___x_1153_);
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
v___jp_1242_:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(5u);
v___x_1245_ = lean_nat_dec_eq(v___x_1153_, v___x_1244_);
if (v___x_1245_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = 1;
v___y_1235_ = v___x_1245_;
v___y_1236_ = v___y_1243_;
v___y_1237_ = v___x_1246_;
goto v___jp_1234_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
v___y_1235_ = v___x_1245_;
v___y_1236_ = v___y_1243_;
v___y_1237_ = v___x_1247_;
goto v___jp_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1251_);
lean_dec_ref(v_a_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_toLocation_1256_, lean_object* v_j_1257_){
_start:
{
lean_object* v_definition_x3f_1259_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1257_);
v___x_1292_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1257_, v___x_1253_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_j_1257_);
lean_dec_ref(v_toLocation_1256_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v___x_1254_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; 
v_a_1301_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1292_, 1);
if (lean_obj_tag(v_a_1301_) == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_box(0);
v_definition_x3f_1259_ = v___x_1302_;
goto v___jp_1258_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1320_; 
v_val_1303_ = lean_ctor_get(v_a_1301_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1301_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1305_ = v_a_1301_;
v_isShared_1306_ = v_isSharedCheck_1320_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_val_1303_);
lean_dec(v_a_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1320_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; 
lean_inc_ref(v_toLocation_1256_);
v___x_1307_ = lean_apply_1(v_toLocation_1256_, v_val_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_del_object(v___x_1305_);
lean_dec(v_j_1257_);
lean_dec_ref(v_toLocation_1256_);
lean_dec_ref(v___x_1255_);
lean_dec_ref(v___x_1254_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1307_, 1);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_a_1316_);
v___x_1318_ = v___x_1305_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_definition_x3f_1259_ = v___x_1318_;
goto v___jp_1258_;
}
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1261_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1257_, v___x_1254_, v___x_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_definition_x3f_1259_);
lean_dec_ref(v_toLocation_1256_);
lean_dec_ref(v___x_1255_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
else
{
lean_object* v_a_1270_; size_t v_sz_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v_a_1270_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1261_, 1);
v_sz_1271_ = lean_array_size(v_a_1270_);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1255_, v_toLocation_1256_, v_sz_1271_, v___x_1272_, v_a_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_definition_x3f_1259_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_definition_x3f_1259_);
lean_ctor_set(v___x_1286_, 1, v_a_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
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
lean_object* v___x_1335_; 
v___x_1335_ = lean_box(1);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(1);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1337_, lean_object* v_a_1338_, lean_object* v_b_1339_, lean_object* v_c_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_a_1338_);
lean_ctor_set(v___x_1341_, 1, v_b_1339_);
v___x_1342_ = lean_apply_2(v_f_1337_, v___x_1341_, v_c_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1343_, lean_object* v_____do__lift_1344_){
_start:
{
lean_object* v_a_1345_; lean_object* v___x_1346_; 
v_a_1345_ = lean_ctor_get(v_____do__lift_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref(v_____do__lift_1344_);
v___x_1346_ = lean_apply_2(v_toPure_1343_, lean_box(0), v_a_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_map_1349_, lean_object* v_init_1350_, lean_object* v_f_1351_){
_start:
{
lean_object* v_toApplicative_1352_; lean_object* v_toBind_1353_; lean_object* v_toPure_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; 
v_toApplicative_1352_ = lean_ctor_get(v_inst_1347_, 0);
v_toBind_1353_ = lean_ctor_get(v_inst_1347_, 1);
lean_inc(v_toBind_1353_);
v_toPure_1354_ = lean_ctor_get(v_toApplicative_1352_, 1);
lean_inc(v_toPure_1354_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1355_, 0, v_f_1351_);
v___x_1356_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1347_, v___f_1355_, v_init_1350_, v_map_1349_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1357_, 0, v_toPure_1354_);
v___x_1358_ = lean_apply_4(v_toBind_1353_, lean_box(0), lean_box(0), v___x_1356_, v___f_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1359_){
_start:
{
lean_object* v___f_1360_; 
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1360_, 0, v_inst_1359_);
return v___f_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1361_, lean_object* v_inst_1362_){
_start:
{
lean_object* v___f_1363_; 
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1363_, 0, v_inst_1362_);
return v___f_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_startPosLine_1366_; lean_object* v_startPosCharacter_1367_; lean_object* v_endPosLine_1368_; lean_object* v_endPosCharacter_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_range_1375_; lean_object* v___x_1376_; 
v_startPosLine_1366_ = lean_ctor_get(v_x_1365_, 0);
v_startPosCharacter_1367_ = lean_ctor_get(v_x_1365_, 1);
v_endPosLine_1368_ = lean_ctor_get(v_x_1365_, 2);
v_endPosCharacter_1369_ = lean_ctor_get(v_x_1365_, 3);
v___x_1370_ = lean_box(0);
lean_inc(v_endPosCharacter_1369_);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_endPosCharacter_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
lean_inc(v_endPosLine_1368_);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_endPosLine_1368_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
lean_inc(v_startPosCharacter_1367_);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_startPosCharacter_1367_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
lean_inc(v_startPosLine_1366_);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_startPosLine_1366_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v_range_1375_ = l_List_mapTR_loop___redArg(v___f_1364_, v___x_1374_, v___x_1370_);
v___x_1376_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1365_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = l_List_appendTR___redArg(v_range_1375_, v___x_1370_);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1387_; 
v_val_1378_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_val_1378_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 3);
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_val_1378_);
v___x_1383_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1370_);
v___x_1385_ = l_List_appendTR___redArg(v_range_1375_, v___x_1384_);
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1388_, lean_object* v_x_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1388_, v_x_1389_);
lean_dec_ref(v_x_1389_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1391_, lean_object* v___f_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_snd_1394_; lean_object* v_fst_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1456_; 
v_snd_1394_ = lean_ctor_get(v_x_1393_, 1);
v_fst_1395_ = lean_ctor_get(v_x_1393_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1393_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1397_ = v_x_1393_;
v_isShared_1398_ = v_isSharedCheck_1456_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1394_);
lean_inc(v_fst_1395_);
lean_dec(v_x_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1456_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_definition_x3f_1399_; lean_object* v_usages_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1455_; 
v_definition_x3f_1399_ = lean_ctor_get(v_snd_1394_, 0);
v_usages_1400_ = lean_ctor_get(v_snd_1394_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_snd_1394_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1402_ = v_snd_1394_;
v_isShared_1403_ = v_isSharedCheck_1455_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_usages_1400_);
lean_inc(v_definition_x3f_1399_);
lean_dec(v_snd_1394_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1455_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1429_; 
v___x_1404_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1395_);
v___x_1405_ = l_Lean_Json_compress(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1407_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1399_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref(v___f_1392_);
v___x_1431_ = lean_box(0);
v___y_1409_ = v___x_1431_;
goto v___jp_1408_;
}
else
{
lean_object* v_val_1432_; lean_object* v_startPosLine_1433_; lean_object* v_startPosCharacter_1434_; lean_object* v_endPosLine_1435_; lean_object* v_endPosCharacter_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_range_1442_; lean_object* v___x_1443_; 
v_val_1432_ = lean_ctor_get(v_definition_x3f_1399_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v_definition_x3f_1399_, 1);
v_startPosLine_1433_ = lean_ctor_get(v_val_1432_, 0);
v_startPosCharacter_1434_ = lean_ctor_get(v_val_1432_, 1);
v_endPosLine_1435_ = lean_ctor_get(v_val_1432_, 2);
v_endPosCharacter_1436_ = lean_ctor_get(v_val_1432_, 3);
v___x_1437_ = lean_box(0);
lean_inc(v_endPosCharacter_1436_);
v___x_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1438_, 0, v_endPosCharacter_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
lean_inc(v_endPosLine_1435_);
v___x_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_endPosLine_1435_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_inc(v_startPosCharacter_1434_);
v___x_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_startPosCharacter_1434_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
lean_inc(v_startPosLine_1433_);
v___x_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_startPosLine_1433_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v_range_1442_ = l_List_mapTR_loop___redArg(v___f_1392_, v___x_1441_, v___x_1437_);
v___x_1443_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1432_);
lean_dec(v_val_1432_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = l_List_appendTR___redArg(v_range_1442_, v___x_1437_);
v___y_1429_ = v___x_1444_;
goto v___jp_1428_;
}
else
{
lean_object* v_val_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1454_; 
v_val_1445_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1447_ = v___x_1443_;
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_val_1445_);
lean_dec(v___x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 3);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_val_1445_);
v___x_1450_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v___x_1437_);
v___x_1452_ = l_List_appendTR___redArg(v_range_1442_, v___x_1451_);
v___y_1429_ = v___x_1452_;
goto v___jp_1428_;
}
}
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = l_Lean_Option_toJson___redArg(v___x_1406_, v___y_1409_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1410_);
lean_ctor_set(v___x_1397_, 0, v___x_1407_);
v___x_1412_ = v___x_1397_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1413_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1414_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1415_ = lean_array_size(v_usages_1400_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v___f_1391_, v_sz_1415_, v___x_1416_, v_usages_1400_);
v___x_1418_ = l_Lean_Array_toJson___redArg(v___x_1406_, v___x_1417_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1418_);
lean_ctor_set(v___x_1402_, 0, v___x_1413_);
v___x_1420_ = v___x_1402_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1412_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_Json_mkObj(v___x_1423_);
lean_dec_ref_known(v___x_1423_, 2);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1405_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
return v___x_1425_;
}
}
}
v___jp_1428_:
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___y_1429_);
v___y_1409_ = v___x_1430_;
goto v___jp_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1457_, lean_object* v_x2_1458_, lean_object* v_x3_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_x1_1457_);
lean_ctor_set(v___x_1460_, 1, v_x2_1458_);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v_x3_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1462_, lean_object* v___f_1463_, lean_object* v_m_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1465_ = lean_box(0);
v___x_1466_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1467_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1466_, v___f_1462_, v___x_1465_, v_m_1464_);
v___x_1468_ = l_List_mapTR_loop___redArg(v___f_1463_, v___x_1467_, v___x_1465_);
v___x_1469_ = l_Lean_Json_mkObj(v___x_1468_);
lean_dec(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1480_, lean_object* v_m_1481_, lean_object* v_k_1482_, lean_object* v_v_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Json_parse(v_k_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
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
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1494_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
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
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_a_1503_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1505_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1506_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1483_);
v___x_1507_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1483_, v___x_1505_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
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
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1647_; 
v_a_1516_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1518_ = v___x_1507_;
v_isShared_1519_ = v_isSharedCheck_1647_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1507_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1647_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v_definition_x3f_1522_; lean_object* v_a_1557_; 
v___x_1520_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1516_) == 0)
{
lean_object* v___x_1559_; 
lean_del_object(v___x_1518_);
v___x_1559_ = lean_box(0);
v_definition_x3f_1522_ = v___x_1559_;
goto v___jp_1521_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___y_1564_; uint8_t v___y_1629_; uint8_t v___y_1630_; uint8_t v___y_1631_; uint8_t v___y_1639_; uint8_t v___x_1644_; 
v_val_1560_ = lean_ctor_get(v_a_1516_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v_a_1516_, 1);
v___x_1561_ = lean_array_get_size(v_val_1560_);
v___x_1562_ = lean_unsigned_to_nat(4u);
v___x_1644_ = lean_nat_dec_eq(v___x_1561_, v___x_1562_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = 1;
v___y_1639_ = v___x_1645_;
goto v___jp_1638_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = 0;
v___y_1639_ = v___x_1646_;
goto v___jp_1638_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_array_fget_borrowed(v_val_1560_, v___x_1565_);
lean_inc(v___x_1566_);
v___x_1567_ = l_Lean_Json_getNat_x3f(v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_val_1560_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_a_1576_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_array_fget_borrowed(v_val_1560_, v___x_1577_);
lean_inc(v___x_1578_);
v___x_1579_ = l_Lean_Json_getNat_x3f(v___x_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1576_);
lean_dec(v_val_1560_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_a_1588_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1589_ = lean_unsigned_to_nat(2u);
v___x_1590_ = lean_array_fget_borrowed(v_val_1560_, v___x_1589_);
lean_inc(v___x_1590_);
v___x_1591_ = l_Lean_Json_getNat_x3f(v___x_1590_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1576_);
lean_dec(v_val_1560_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1600_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1601_ = lean_unsigned_to_nat(3u);
v___x_1602_ = lean_array_fget_borrowed(v_val_1560_, v___x_1601_);
lean_inc(v___x_1602_);
v___x_1603_ = l_Lean_Json_getNat_x3f(v___x_1602_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1600_);
lean_dec(v_a_1588_);
lean_dec(v_a_1576_);
lean_dec(v_val_1560_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
if (v___y_1564_ == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec(v_val_1560_);
v_a_1612_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1613_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1614_, 0, v_a_1576_);
lean_ctor_set(v___x_1614_, 1, v_a_1588_);
lean_ctor_set(v___x_1614_, 2, v_a_1600_);
lean_ctor_set(v___x_1614_, 3, v_a_1612_);
lean_ctor_set(v___x_1614_, 4, v___x_1613_);
v_a_1557_ = v___x_1614_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1616_ = lean_array_fget(v_val_1560_, v___x_1562_);
lean_dec(v_val_1560_);
v___x_1617_ = l_Lean_Json_getStr_x3f(v___x_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1615_);
lean_dec(v_a_1600_);
lean_dec(v_a_1588_);
lean_dec(v_a_1576_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1576_);
lean_ctor_set(v___x_1627_, 1, v_a_1588_);
lean_ctor_set(v___x_1627_, 2, v_a_1600_);
lean_ctor_set(v___x_1627_, 3, v_a_1615_);
lean_ctor_set(v___x_1627_, 4, v_a_1626_);
v_a_1557_ = v___x_1627_;
goto v___jp_1556_;
}
}
}
}
}
}
}
v___jp_1628_:
{
if (v___y_1629_ == 0)
{
lean_del_object(v___x_1518_);
v___y_1564_ = v___y_1630_;
goto v___jp_1563_;
}
else
{
if (v___y_1631_ == 0)
{
lean_del_object(v___x_1518_);
v___y_1564_ = v___y_1630_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_dec(v_val_1560_);
lean_dec(v_a_1503_);
lean_dec(v_v_1483_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
v___x_1632_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1633_ = l_Nat_reprFast(v___x_1561_);
v___x_1634_ = lean_string_append(v___x_1632_, v___x_1633_);
lean_dec_ref(v___x_1633_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1634_);
v___x_1636_ = v___x_1518_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
v___jp_1638_:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = lean_unsigned_to_nat(5u);
v___x_1641_ = lean_nat_dec_eq(v___x_1561_, v___x_1640_);
if (v___x_1641_ == 0)
{
uint8_t v___x_1642_; 
v___x_1642_ = 1;
v___y_1629_ = v___y_1639_;
v___y_1630_ = v___x_1641_;
v___y_1631_ = v___x_1642_;
goto v___jp_1628_;
}
else
{
uint8_t v___x_1643_; 
v___x_1643_ = 0;
v___y_1629_ = v___y_1639_;
v___y_1630_ = v___x_1641_;
v___y_1631_ = v___x_1643_;
goto v___jp_1628_;
}
}
}
v___jp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1524_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1483_, v___x_1520_, v___x_1523_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_definition_x3f_1522_);
lean_dec(v_a_1503_);
lean_dec(v_m_1481_);
lean_dec_ref(v_toLocation_1480_);
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
lean_object* v_a_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1524_, 1);
v_sz_1534_ = lean_array_size(v_a_1533_);
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1504_, v_toLocation_1480_, v_sz_1534_, v___x_1535_, v_a_1533_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_definition_x3f_1522_);
lean_dec(v_a_1503_);
lean_dec(v_m_1481_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_a_1545_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1547_ = v___x_1536_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1536_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_definition_x3f_1522_);
lean_ctor_set(v___x_1549_, 1, v_a_1545_);
v___x_1550_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1551_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1550_, v_a_1503_, v___x_1549_, v_m_1481_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1551_);
v___x_1553_ = v___x_1547_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1557_);
v_definition_x3f_1522_ = v___x_1558_;
goto v___jp_1521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1648_, lean_object* v___f_1649_, lean_object* v_j_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Json_getObj_x3f(v_j_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___f_1649_);
lean_dec_ref(v___x_1648_);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_a_1660_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1661_ = lean_box(1);
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1648_, v___f_1649_, v___x_1661_, v_a_1660_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1669_, lean_object* v_k_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = l_Lean_Json_getObjValD(v_j_1669_, v_k_1670_);
v___x_1672_ = l_Lean_Json_getNat_x3f(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1673_, lean_object* v_k_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1673_, v_k_1674_);
lean_dec_ref(v_k_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = l_Lean_Json_getObjValD(v_j_1676_, v_k_1677_);
v___x_1679_ = l_Lean_Json_getBool_x3f(v___x_1678_);
lean_dec(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1680_, lean_object* v_k_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1680_, v_k_1681_);
lean_dec_ref(v_k_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_bs_1687_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_bs_1687_);
return v___x_1691_;
}
else
{
lean_object* v_v_1692_; 
v_v_1692_ = lean_array_uget_borrowed(v_bs_1687_, v_i_1686_);
if (lean_obj_tag(v_v_1692_) == 4)
{
lean_object* v_elems_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_elems_1693_ = lean_ctor_get(v_v_1692_, 0);
v___x_1694_ = lean_array_get_size(v_elems_1693_);
v___x_1695_ = lean_unsigned_to_nat(4u);
v___x_1696_ = lean_nat_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v_bs_1687_);
goto v___jp_1688_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_array_fget_borrowed(v_elems_1693_, v___x_1697_);
lean_inc(v___x_1698_);
v___x_1699_ = l_Lean_Json_getStr_x3f(v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v_bs_1687_);
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_a_1708_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_array_fget_borrowed(v_elems_1693_, v___x_1709_);
v___x_1711_ = l_Lean_Json_getBool_x3f(v___x_1710_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1708_);
lean_dec_ref(v_bs_1687_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1720_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1721_ = lean_unsigned_to_nat(2u);
v___x_1722_ = lean_array_fget_borrowed(v_elems_1693_, v___x_1721_);
v___x_1723_ = l_Lean_Json_getBool_x3f(v___x_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_a_1720_);
lean_dec(v_a_1708_);
lean_dec_ref(v_bs_1687_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_a_1732_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1733_ = lean_unsigned_to_nat(3u);
v___x_1734_ = lean_array_fget_borrowed(v_elems_1693_, v___x_1733_);
v___x_1735_ = l_Lean_Json_getBool_x3f(v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1732_);
lean_dec(v_a_1720_);
lean_dec(v_a_1708_);
lean_dec_ref(v_bs_1687_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v_bs_x27_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1744_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1735_, 1);
v_bs_x27_1745_ = lean_array_uset(v_bs_1687_, v_i_1686_, v___x_1697_);
v___x_1746_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1746_, 0, v_a_1708_);
v___x_1747_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1, v___x_1747_);
v___x_1748_ = lean_unbox(v_a_1732_);
lean_dec(v_a_1732_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1 + 1, v___x_1748_);
v___x_1749_ = lean_unbox(v_a_1744_);
lean_dec(v_a_1744_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*1 + 2, v___x_1749_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1686_, v___x_1750_);
v___x_1752_ = lean_array_uset(v_bs_x27_1745_, v_i_1686_, v___x_1746_);
v_i_1686_ = v___x_1751_;
v_bs_1687_ = v___x_1752_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1687_);
goto v___jp_1688_;
}
}
v___jp_1688_:
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_bs_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1756_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1762_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 4)
{
lean_object* v_elems_1763_; size_t v_sz_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v_elems_1763_ = lean_ctor_get(v_x_1762_, 0);
lean_inc_ref(v_elems_1763_);
lean_dec_ref_known(v_x_1762_, 1);
v_sz_1764_ = lean_array_size(v_elems_1763_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1764_, v___x_1765_, v_elems_1763_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1767_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1768_ = lean_unsigned_to_nat(80u);
v___x_1769_ = l_Lean_Json_pretty(v_x_1762_, v___x_1768_);
v___x_1770_ = lean_string_append(v___x_1767_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1774_, lean_object* v_k_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = l_Lean_Json_getObjValD(v_j_1774_, v_k_1775_);
v___x_1777_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1778_, lean_object* v_k_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1778_, v_k_1779_);
lean_dec_ref(v_k_1779_);
return v_res_1780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = 1;
v___x_1790_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1794_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1795_ = lean_string_append(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = 1;
v___x_1799_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1800_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1803_ = lean_string_append(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1806_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1807_ = lean_string_append(v___x_1806_, v___x_1805_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = 1;
v___x_1812_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1815_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1816_ = lean_string_append(v___x_1815_, v___x_1814_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1819_ = lean_string_append(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = 1;
v___x_1824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1825_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1828_ = lean_string_append(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1832_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1832_);
v___x_1834_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1832_, v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_json_1832_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1844_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1840_ = lean_string_append(v___x_1839_, v_a_1835_);
lean_dec(v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_json_1832_);
v_a_1845_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1834_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1834_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 0);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
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
v_a_1853_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1832_);
v___x_1855_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1832_, v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1853_);
lean_dec(v_json_1832_);
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
v___x_1860_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
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
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_a_1853_);
lean_dec(v_json_1832_);
v_a_1866_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1855_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1855_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 0);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1874_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1875_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1876_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1832_, v___x_1875_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1874_);
lean_dec(v_a_1853_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1882_ = lean_string_append(v___x_1881_, v_a_1877_);
lean_dec(v_a_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
else
{
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_a_1874_);
lean_dec(v_a_1853_);
v_a_1887_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1876_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1876_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1904_; 
v_a_1895_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1897_ = v___x_1876_;
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1876_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1899_, 0, v_a_1853_);
lean_ctor_set(v___x_1899_, 1, v_a_1895_);
v___x_1900_ = lean_unbox(v_a_1874_);
lean_dec(v_a_1874_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*2, v___x_1900_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1899_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1899_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_bs_1909_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_lt(v_i_1908_, v_sz_1907_);
if (v___x_1910_ == 0)
{
return v_bs_1909_;
}
else
{
lean_object* v_v_1911_; lean_object* v_module_1912_; uint8_t v_isPrivate_1913_; uint8_t v_isAll_1914_; uint8_t v_isMeta_1915_; lean_object* v___x_1916_; lean_object* v_bs_x27_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v_v_1911_ = lean_array_uget_borrowed(v_bs_1909_, v_i_1908_);
v_module_1912_ = lean_ctor_get(v_v_1911_, 0);
lean_inc_ref(v_module_1912_);
v_isPrivate_1913_ = lean_ctor_get_uint8(v_v_1911_, sizeof(void*)*1);
v_isAll_1914_ = lean_ctor_get_uint8(v_v_1911_, sizeof(void*)*1 + 1);
v_isMeta_1915_ = lean_ctor_get_uint8(v_v_1911_, sizeof(void*)*1 + 2);
v___x_1916_ = lean_unsigned_to_nat(0u);
v_bs_x27_1917_ = lean_array_uset(v_bs_1909_, v_i_1908_, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_module_1912_);
v___x_1919_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1919_, 0, v_isPrivate_1913_);
v___x_1920_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1920_, 0, v_isAll_1914_);
v___x_1921_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1921_, 0, v_isMeta_1915_);
v___x_1922_ = lean_unsigned_to_nat(4u);
v___x_1923_ = lean_mk_empty_array_with_capacity(v___x_1922_);
v___x_1924_ = lean_array_push(v___x_1923_, v___x_1918_);
v___x_1925_ = lean_array_push(v___x_1924_, v___x_1919_);
v___x_1926_ = lean_array_push(v___x_1925_, v___x_1920_);
v___x_1927_ = lean_array_push(v___x_1926_, v___x_1921_);
v___x_1928_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_add(v_i_1908_, v___x_1929_);
v___x_1931_ = lean_array_uset(v_bs_x27_1917_, v_i_1908_, v___x_1928_);
v_i_1908_ = v___x_1930_;
v_bs_1909_ = v___x_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1933_, lean_object* v_i_1934_, lean_object* v_bs_1935_){
_start:
{
size_t v_sz_boxed_1936_; size_t v_i_boxed_1937_; lean_object* v_res_1938_; 
v_sz_boxed_1936_ = lean_unbox_usize(v_sz_1933_);
lean_dec(v_sz_1933_);
v_i_boxed_1937_ = lean_unbox_usize(v_i_1934_);
lean_dec(v_i_1934_);
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1936_, v_i_boxed_1937_, v_bs_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1939_){
_start:
{
size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_sz_1940_ = lean_array_size(v_a_1939_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1940_, v___x_1941_, v_a_1939_);
v___x_1943_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
if (lean_obj_tag(v_a_1944_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_array_to_list(v_a_1945_);
return v___x_1946_;
}
else
{
lean_object* v_head_1947_; lean_object* v_tail_1948_; lean_object* v___x_1949_; 
v_head_1947_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_head_1947_);
v_tail_1948_ = lean_ctor_get(v_a_1944_, 1);
lean_inc(v_tail_1948_);
lean_dec_ref_known(v_a_1944_, 2);
v___x_1949_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1945_, v_head_1947_);
v_a_1944_ = v_tail_1948_;
v_a_1945_ = v___x_1949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1953_){
_start:
{
lean_object* v_version_1954_; uint8_t v_isSetupFailure_1955_; lean_object* v_directImports_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_version_1954_ = lean_ctor_get(v_x_1953_, 0);
lean_inc(v_version_1954_);
v_isSetupFailure_1955_ = lean_ctor_get_uint8(v_x_1953_, sizeof(void*)*2);
v_directImports_1956_ = lean_ctor_get(v_x_1953_, 1);
lean_inc_ref(v_directImports_1956_);
lean_dec_ref(v_x_1953_);
v___x_1957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1958_ = l_Lean_JsonNumber_fromNat(v_version_1954_);
v___x_1959_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1957_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1964_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1964_, 0, v_isSetupFailure_1955_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1961_);
v___x_1967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1968_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1956_);
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1961_);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1961_);
v___x_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1966_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1962_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1975_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1973_, v___x_1974_);
v___x_1976_ = l_Lean_Json_mkObj(v___x_1975_);
lean_dec(v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1979_, lean_object* v_v_1980_, lean_object* v_t_1981_){
_start:
{
if (lean_obj_tag(v_t_1981_) == 0)
{
lean_object* v_size_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v_l_1985_; lean_object* v_r_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2266_; 
v_size_1982_ = lean_ctor_get(v_t_1981_, 0);
v_k_1983_ = lean_ctor_get(v_t_1981_, 1);
v_v_1984_ = lean_ctor_get(v_t_1981_, 2);
v_l_1985_ = lean_ctor_get(v_t_1981_, 3);
v_r_1986_ = lean_ctor_get(v_t_1981_, 4);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_t_1981_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_1988_ = v_t_1981_;
v_isShared_1989_ = v_isSharedCheck_2266_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_r_1986_);
lean_inc(v_l_1985_);
lean_inc(v_v_1984_);
lean_inc(v_k_1983_);
lean_inc(v_size_1982_);
lean_dec(v_t_1981_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2266_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_string_compare(v_k_1979_, v_k_1983_);
switch(v___x_1990_)
{
case 0:
{
lean_object* v_impl_1991_; lean_object* v___x_1992_; 
lean_dec(v_size_1982_);
v_impl_1991_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1979_, v_v_1980_, v_l_1985_);
v___x_1992_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1986_) == 0)
{
lean_object* v_size_1993_; lean_object* v_size_1994_; lean_object* v_k_1995_; lean_object* v_v_1996_; lean_object* v_l_1997_; lean_object* v_r_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_size_1993_ = lean_ctor_get(v_r_1986_, 0);
v_size_1994_ = lean_ctor_get(v_impl_1991_, 0);
lean_inc(v_size_1994_);
v_k_1995_ = lean_ctor_get(v_impl_1991_, 1);
lean_inc(v_k_1995_);
v_v_1996_ = lean_ctor_get(v_impl_1991_, 2);
lean_inc(v_v_1996_);
v_l_1997_ = lean_ctor_get(v_impl_1991_, 3);
lean_inc(v_l_1997_);
v_r_1998_ = lean_ctor_get(v_impl_1991_, 4);
lean_inc(v_r_1998_);
v___x_1999_ = lean_unsigned_to_nat(3u);
v___x_2000_ = lean_nat_mul(v___x_1999_, v_size_1993_);
v___x_2001_ = lean_nat_dec_lt(v___x_2000_, v_size_1994_);
lean_dec(v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_dec(v_r_1998_);
lean_dec(v_l_1997_);
lean_dec(v_v_1996_);
lean_dec(v_k_1995_);
v___x_2002_ = lean_nat_add(v___x_1992_, v_size_1994_);
lean_dec(v_size_1994_);
v___x_2003_ = lean_nat_add(v___x_2002_, v_size_1993_);
lean_dec(v___x_2002_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 3, v_impl_1991_);
lean_ctor_set(v___x_1988_, 0, v___x_2003_);
v___x_2005_ = v___x_1988_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_impl_1991_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_r_1986_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
else
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2072_; 
v_isSharedCheck_2072_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2073_ = lean_ctor_get(v_impl_1991_, 4);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_impl_1991_, 2);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_impl_1991_, 1);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2077_);
v___x_2008_ = v_impl_1991_;
v_isShared_2009_ = v_isSharedCheck_2072_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_impl_1991_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2072_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_size_2010_; lean_object* v_size_2011_; lean_object* v_k_2012_; lean_object* v_v_2013_; lean_object* v_l_2014_; lean_object* v_r_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_size_2010_ = lean_ctor_get(v_l_1997_, 0);
v_size_2011_ = lean_ctor_get(v_r_1998_, 0);
v_k_2012_ = lean_ctor_get(v_r_1998_, 1);
v_v_2013_ = lean_ctor_get(v_r_1998_, 2);
v_l_2014_ = lean_ctor_get(v_r_1998_, 3);
v_r_2015_ = lean_ctor_get(v_r_1998_, 4);
v___x_2016_ = lean_unsigned_to_nat(2u);
v___x_2017_ = lean_nat_mul(v___x_2016_, v_size_2010_);
v___x_2018_ = lean_nat_dec_lt(v_size_2011_, v___x_2017_);
lean_dec(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2047_; 
lean_inc(v_r_2015_);
lean_inc(v_l_2014_);
lean_inc(v_v_2013_);
lean_inc(v_k_2012_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_r_1998_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2048_ = lean_ctor_get(v_r_1998_, 4);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_r_1998_, 3);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_r_1998_, 2);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_r_1998_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_r_1998_, 0);
lean_dec(v_unused_2052_);
v___x_2020_ = v_r_1998_;
v_isShared_2021_ = v_isSharedCheck_2047_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v_r_1998_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2047_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___x_2035_; lean_object* v___y_2037_; 
v___x_2022_ = lean_nat_add(v___x_1992_, v_size_1994_);
lean_dec(v_size_1994_);
v___x_2023_ = lean_nat_add(v___x_2022_, v_size_1993_);
lean_dec(v___x_2022_);
v___x_2035_ = lean_nat_add(v___x_1992_, v_size_2010_);
if (lean_obj_tag(v_l_2014_) == 0)
{
lean_object* v_size_2045_; 
v_size_2045_ = lean_ctor_get(v_l_2014_, 0);
lean_inc(v_size_2045_);
v___y_2037_ = v_size_2045_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___y_2037_ = v___x_2046_;
goto v___jp_2036_;
}
v___jp_2024_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_nat_add(v___y_2025_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec(v___y_2025_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 4, v_r_1986_);
lean_ctor_set(v___x_2020_, 3, v_r_2015_);
lean_ctor_set(v___x_2020_, 2, v_v_1984_);
lean_ctor_set(v___x_2020_, 1, v_k_1983_);
lean_ctor_set(v___x_2020_, 0, v___x_2028_);
v___x_2030_ = v___x_2020_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_r_2015_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_r_1986_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2030_);
lean_ctor_set(v___x_2008_, 3, v___y_2026_);
lean_ctor_set(v___x_2008_, 2, v_v_2013_);
lean_ctor_set(v___x_2008_, 1, v_k_2012_);
lean_ctor_set(v___x_2008_, 0, v___x_2023_);
v___x_2032_ = v___x_2008_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_2012_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_2013_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___y_2026_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
v___jp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_nat_add(v___x_2035_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec(v___x_2035_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_l_2014_);
lean_ctor_set(v___x_1988_, 3, v_l_1997_);
lean_ctor_set(v___x_1988_, 2, v_v_1996_);
lean_ctor_set(v___x_1988_, 1, v_k_1995_);
lean_ctor_set(v___x_1988_, 0, v___x_2038_);
v___x_2040_ = v___x_1988_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_1997_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_l_2014_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_nat_add(v___x_1992_, v_size_1993_);
if (lean_obj_tag(v_r_2015_) == 0)
{
lean_object* v_size_2042_; 
v_size_2042_ = lean_ctor_get(v_r_2015_, 0);
lean_inc(v_size_2042_);
v___y_2025_ = v___x_2041_;
v___y_2026_ = v___x_2040_;
v___y_2027_ = v_size_2042_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_unsigned_to_nat(0u);
v___y_2025_ = v___x_2041_;
v___y_2026_ = v___x_2040_;
v___y_2027_ = v___x_2043_;
goto v___jp_2024_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_del_object(v___x_1988_);
v___x_2053_ = lean_nat_add(v___x_1992_, v_size_1994_);
lean_dec(v_size_1994_);
v___x_2054_ = lean_nat_add(v___x_2053_, v_size_1993_);
lean_dec(v___x_2053_);
v___x_2055_ = lean_nat_add(v___x_1992_, v_size_1993_);
v___x_2056_ = lean_nat_add(v___x_2055_, v_size_2011_);
lean_dec(v___x_2055_);
lean_inc_ref(v_r_1986_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_r_1986_);
lean_ctor_set(v___x_2008_, 3, v_r_1998_);
lean_ctor_set(v___x_2008_, 2, v_v_1984_);
lean_ctor_set(v___x_2008_, 1, v_k_1983_);
lean_ctor_set(v___x_2008_, 0, v___x_2056_);
v___x_2058_ = v___x_2008_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_r_1998_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_r_1986_);
v___x_2058_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v_r_1986_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; 
v_unused_2066_ = lean_ctor_get(v_r_1986_, 4);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_r_1986_, 3);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_r_1986_, 2);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_r_1986_, 1);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_r_1986_, 0);
lean_dec(v_unused_2070_);
v___x_2060_ = v_r_1986_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_r_1986_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2058_);
lean_ctor_set(v___x_2060_, 3, v_l_1997_);
lean_ctor_set(v___x_2060_, 2, v_v_1996_);
lean_ctor_set(v___x_2060_, 1, v_k_1995_);
lean_ctor_set(v___x_2060_, 0, v___x_2054_);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_l_1997_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v___x_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2078_; 
v_l_2078_ = lean_ctor_get(v_impl_1991_, 3);
lean_inc(v_l_2078_);
if (lean_obj_tag(v_l_2078_) == 0)
{
lean_object* v_r_2079_; lean_object* v_k_2080_; lean_object* v_v_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2092_; 
v_r_2079_ = lean_ctor_get(v_impl_1991_, 4);
v_k_2080_ = lean_ctor_get(v_impl_1991_, 1);
v_v_2081_ = lean_ctor_get(v_impl_1991_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2093_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2094_);
v___x_2083_ = v_impl_1991_;
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_r_2079_);
lean_inc(v_v_2081_);
lean_inc(v_k_2080_);
lean_dec(v_impl_1991_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2079_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 3, v_r_2079_);
lean_ctor_set(v___x_2083_, 2, v_v_1984_);
lean_ctor_set(v___x_2083_, 1, v_k_1983_);
lean_ctor_set(v___x_2083_, 0, v___x_1992_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_r_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_r_2079_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2087_);
lean_ctor_set(v___x_1988_, 3, v_l_2078_);
lean_ctor_set(v___x_1988_, 2, v_v_2081_);
lean_ctor_set(v___x_1988_, 1, v_k_2080_);
lean_ctor_set(v___x_1988_, 0, v___x_2085_);
v___x_2089_ = v___x_1988_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_l_2078_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_r_2095_; 
v_r_2095_ = lean_ctor_get(v_impl_1991_, 4);
lean_inc(v_r_2095_);
if (lean_obj_tag(v_r_2095_) == 0)
{
lean_object* v_k_2096_; lean_object* v_v_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2120_; 
v_k_2096_ = lean_ctor_get(v_impl_1991_, 1);
v_v_2097_ = lean_ctor_get(v_impl_1991_, 2);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; 
v_unused_2121_ = lean_ctor_get(v_impl_1991_, 4);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2123_);
v___x_2099_ = v_impl_1991_;
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_v_2097_);
lean_inc(v_k_2096_);
lean_dec(v_impl_1991_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_k_2101_; lean_object* v_v_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2116_; 
v_k_2101_ = lean_ctor_get(v_r_2095_, 1);
v_v_2102_ = lean_ctor_get(v_r_2095_, 2);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_r_2095_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; 
v_unused_2117_ = lean_ctor_get(v_r_2095_, 4);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_r_2095_, 3);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_r_2095_, 0);
lean_dec(v_unused_2119_);
v___x_2104_ = v_r_2095_;
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
lean_dec(v_r_2095_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2116_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_unsigned_to_nat(3u);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 4, v_l_2078_);
lean_ctor_set(v___x_2104_, 3, v_l_2078_);
lean_ctor_set(v___x_2104_, 2, v_v_2097_);
lean_ctor_set(v___x_2104_, 1, v_k_2096_);
lean_ctor_set(v___x_2104_, 0, v___x_1992_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_l_2078_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_l_2078_);
v___x_2108_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_l_2078_);
lean_ctor_set(v___x_2099_, 2, v_v_1984_);
lean_ctor_set(v___x_2099_, 1, v_k_1983_);
lean_ctor_set(v___x_2099_, 0, v___x_1992_);
v___x_2110_ = v___x_2099_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_l_2078_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_l_2078_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2110_);
lean_ctor_set(v___x_1988_, 3, v___x_2108_);
lean_ctor_set(v___x_1988_, 2, v_v_2102_);
lean_ctor_set(v___x_1988_, 1, v_k_2101_);
lean_ctor_set(v___x_1988_, 0, v___x_2106_);
v___x_2112_ = v___x_1988_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(2u);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_r_2095_);
lean_ctor_set(v___x_1988_, 3, v_impl_1991_);
lean_ctor_set(v___x_1988_, 0, v___x_2124_);
v___x_2126_ = v___x_1988_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_impl_1991_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v_r_2095_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2129_; 
lean_dec(v_v_1984_);
lean_dec(v_k_1983_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 2, v_v_1980_);
lean_ctor_set(v___x_1988_, 1, v_k_1979_);
v___x_2129_ = v___x_1988_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_size_1982_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_r_1986_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
default: 
{
lean_object* v_impl_2131_; lean_object* v___x_2132_; 
lean_dec(v_size_1982_);
v_impl_2131_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1979_, v_v_1980_, v_r_1986_);
v___x_2132_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1985_) == 0)
{
lean_object* v_size_2133_; lean_object* v_size_2134_; lean_object* v_k_2135_; lean_object* v_v_2136_; lean_object* v_l_2137_; lean_object* v_r_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_size_2133_ = lean_ctor_get(v_l_1985_, 0);
v_size_2134_ = lean_ctor_get(v_impl_2131_, 0);
lean_inc(v_size_2134_);
v_k_2135_ = lean_ctor_get(v_impl_2131_, 1);
lean_inc(v_k_2135_);
v_v_2136_ = lean_ctor_get(v_impl_2131_, 2);
lean_inc(v_v_2136_);
v_l_2137_ = lean_ctor_get(v_impl_2131_, 3);
lean_inc(v_l_2137_);
v_r_2138_ = lean_ctor_get(v_impl_2131_, 4);
lean_inc(v_r_2138_);
v___x_2139_ = lean_unsigned_to_nat(3u);
v___x_2140_ = lean_nat_mul(v___x_2139_, v_size_2133_);
v___x_2141_ = lean_nat_dec_lt(v___x_2140_, v_size_2134_);
lean_dec(v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_dec(v_r_2138_);
lean_dec(v_l_2137_);
lean_dec(v_v_2136_);
lean_dec(v_k_2135_);
v___x_2142_ = lean_nat_add(v___x_2132_, v_size_2133_);
v___x_2143_ = lean_nat_add(v___x_2142_, v_size_2134_);
lean_dec(v_size_2134_);
lean_dec(v___x_2142_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_impl_2131_);
lean_ctor_set(v___x_1988_, 0, v___x_2143_);
v___x_2145_ = v___x_1988_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_impl_2131_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
else
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v_impl_2131_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2211_ = lean_ctor_get(v_impl_2131_, 4);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_impl_2131_, 3);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_impl_2131_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_impl_2131_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_impl_2131_, 0);
lean_dec(v_unused_2215_);
v___x_2148_ = v_impl_2131_;
v_isShared_2149_ = v_isSharedCheck_2210_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v_impl_2131_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2210_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_size_2150_; lean_object* v_k_2151_; lean_object* v_v_2152_; lean_object* v_l_2153_; lean_object* v_r_2154_; lean_object* v_size_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_size_2150_ = lean_ctor_get(v_l_2137_, 0);
v_k_2151_ = lean_ctor_get(v_l_2137_, 1);
v_v_2152_ = lean_ctor_get(v_l_2137_, 2);
v_l_2153_ = lean_ctor_get(v_l_2137_, 3);
v_r_2154_ = lean_ctor_get(v_l_2137_, 4);
v_size_2155_ = lean_ctor_get(v_r_2138_, 0);
v___x_2156_ = lean_unsigned_to_nat(2u);
v___x_2157_ = lean_nat_mul(v___x_2156_, v_size_2155_);
v___x_2158_ = lean_nat_dec_lt(v_size_2150_, v___x_2157_);
lean_dec(v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2186_; 
lean_inc(v_r_2154_);
lean_inc(v_l_2153_);
lean_inc(v_v_2152_);
lean_inc(v_k_2151_);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_l_2137_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2187_ = lean_ctor_get(v_l_2137_, 4);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_l_2137_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_l_2137_, 2);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_2137_, 1);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_l_2137_, 0);
lean_dec(v_unused_2191_);
v___x_2160_ = v_l_2137_;
v_isShared_2161_ = v_isSharedCheck_2186_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v_l_2137_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2186_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2176_; 
v___x_2162_ = lean_nat_add(v___x_2132_, v_size_2133_);
v___x_2163_ = lean_nat_add(v___x_2162_, v_size_2134_);
lean_dec(v_size_2134_);
if (lean_obj_tag(v_l_2153_) == 0)
{
lean_object* v_size_2184_; 
v_size_2184_ = lean_ctor_get(v_l_2153_, 0);
lean_inc(v_size_2184_);
v___y_2176_ = v_size_2184_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_unsigned_to_nat(0u);
v___y_2176_ = v___x_2185_;
goto v___jp_2175_;
}
v___jp_2164_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_nat_add(v___y_2165_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec(v___y_2165_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 4, v_r_2138_);
lean_ctor_set(v___x_2160_, 3, v_r_2154_);
lean_ctor_set(v___x_2160_, 2, v_v_2136_);
lean_ctor_set(v___x_2160_, 1, v_k_2135_);
lean_ctor_set(v___x_2160_, 0, v___x_2168_);
v___x_2170_ = v___x_2160_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_r_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_r_2138_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 4, v___x_2170_);
lean_ctor_set(v___x_2148_, 3, v___y_2166_);
lean_ctor_set(v___x_2148_, 2, v_v_2152_);
lean_ctor_set(v___x_2148_, 1, v_k_2151_);
lean_ctor_set(v___x_2148_, 0, v___x_2163_);
v___x_2172_ = v___x_2148_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_2151_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_2152_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v___y_2166_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
v___jp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_nat_add(v___x_2162_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec(v___x_2162_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_l_2153_);
lean_ctor_set(v___x_1988_, 0, v___x_2177_);
v___x_2179_ = v___x_1988_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v_l_2153_);
v___x_2179_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_nat_add(v___x_2132_, v_size_2155_);
if (lean_obj_tag(v_r_2154_) == 0)
{
lean_object* v_size_2181_; 
v_size_2181_ = lean_ctor_get(v_r_2154_, 0);
lean_inc(v_size_2181_);
v___y_2165_ = v___x_2180_;
v___y_2166_ = v___x_2179_;
v___y_2167_ = v_size_2181_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___y_2165_ = v___x_2180_;
v___y_2166_ = v___x_2179_;
v___y_2167_ = v___x_2182_;
goto v___jp_2164_;
}
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_del_object(v___x_1988_);
v___x_2192_ = lean_nat_add(v___x_2132_, v_size_2133_);
v___x_2193_ = lean_nat_add(v___x_2192_, v_size_2134_);
lean_dec(v_size_2134_);
v___x_2194_ = lean_nat_add(v___x_2192_, v_size_2150_);
lean_dec(v___x_2192_);
lean_inc_ref(v_l_1985_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 4, v_l_2137_);
lean_ctor_set(v___x_2148_, 3, v_l_1985_);
lean_ctor_set(v___x_2148_, 2, v_v_1984_);
lean_ctor_set(v___x_2148_, 1, v_k_1983_);
lean_ctor_set(v___x_2148_, 0, v___x_2194_);
v___x_2196_ = v___x_2148_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_1985_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_l_2137_);
v___x_2196_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v_l_1985_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2204_ = lean_ctor_get(v_l_1985_, 4);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_l_1985_, 3);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_l_1985_, 2);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_l_1985_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_l_1985_, 0);
lean_dec(v_unused_2208_);
v___x_2198_ = v_l_1985_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_l_1985_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v_r_2138_);
lean_ctor_set(v___x_2198_, 3, v___x_2196_);
lean_ctor_set(v___x_2198_, 2, v_v_2136_);
lean_ctor_set(v___x_2198_, 1, v_k_2135_);
lean_ctor_set(v___x_2198_, 0, v___x_2193_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_r_2138_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2216_; 
v_l_2216_ = lean_ctor_get(v_impl_2131_, 3);
lean_inc(v_l_2216_);
if (lean_obj_tag(v_l_2216_) == 0)
{
lean_object* v_r_2217_; lean_object* v_k_2218_; lean_object* v_v_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2242_; 
v_r_2217_ = lean_ctor_get(v_impl_2131_, 4);
v_k_2218_ = lean_ctor_get(v_impl_2131_, 1);
v_v_2219_ = lean_ctor_get(v_impl_2131_, 2);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_impl_2131_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2243_ = lean_ctor_get(v_impl_2131_, 3);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_impl_2131_, 0);
lean_dec(v_unused_2244_);
v___x_2221_ = v_impl_2131_;
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_r_2217_);
lean_inc(v_v_2219_);
lean_inc(v_k_2218_);
lean_dec(v_impl_2131_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_k_2223_; lean_object* v_v_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2238_; 
v_k_2223_ = lean_ctor_get(v_l_2216_, 1);
v_v_2224_ = lean_ctor_get(v_l_2216_, 2);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_l_2216_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; lean_object* v_unused_2240_; lean_object* v_unused_2241_; 
v_unused_2239_ = lean_ctor_get(v_l_2216_, 4);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v_l_2216_, 3);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2216_, 0);
lean_dec(v_unused_2241_);
v___x_2226_ = v_l_2216_;
v_isShared_2227_ = v_isSharedCheck_2238_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_v_2224_);
lean_inc(v_k_2223_);
lean_dec(v_l_2216_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2238_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2217_, 2);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 4, v_r_2217_);
lean_ctor_set(v___x_2226_, 3, v_r_2217_);
lean_ctor_set(v___x_2226_, 2, v_v_1984_);
lean_ctor_set(v___x_2226_, 1, v_k_1983_);
lean_ctor_set(v___x_2226_, 0, v___x_2132_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_r_2217_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_r_2217_);
v___x_2230_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
lean_inc(v_r_2217_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v_r_2217_);
lean_ctor_set(v___x_2221_, 0, v___x_2132_);
v___x_2232_ = v___x_2221_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_2218_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_2219_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_r_2217_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_r_2217_);
v___x_2232_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v___x_2232_);
lean_ctor_set(v___x_1988_, 3, v___x_2230_);
lean_ctor_set(v___x_1988_, 2, v_v_2224_);
lean_ctor_set(v___x_1988_, 1, v_k_2223_);
lean_ctor_set(v___x_1988_, 0, v___x_2228_);
v___x_2234_ = v___x_1988_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_2223_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_2224_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
else
{
lean_object* v_r_2245_; 
v_r_2245_ = lean_ctor_get(v_impl_2131_, 4);
lean_inc(v_r_2245_);
if (lean_obj_tag(v_r_2245_) == 0)
{
lean_object* v_k_2246_; lean_object* v_v_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2258_; 
v_k_2246_ = lean_ctor_get(v_impl_2131_, 1);
v_v_2247_ = lean_ctor_get(v_impl_2131_, 2);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_impl_2131_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; lean_object* v_unused_2260_; lean_object* v_unused_2261_; 
v_unused_2259_ = lean_ctor_get(v_impl_2131_, 4);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_impl_2131_, 3);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2131_, 0);
lean_dec(v_unused_2261_);
v___x_2249_ = v_impl_2131_;
v_isShared_2250_ = v_isSharedCheck_2258_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_v_2247_);
lean_inc(v_k_2246_);
lean_dec(v_impl_2131_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2258_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = lean_unsigned_to_nat(3u);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 4, v_l_2216_);
lean_ctor_set(v___x_2249_, 2, v_v_1984_);
lean_ctor_set(v___x_2249_, 1, v_k_1983_);
lean_ctor_set(v___x_2249_, 0, v___x_2132_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_l_2216_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_r_2245_);
lean_ctor_set(v___x_1988_, 3, v___x_2253_);
lean_ctor_set(v___x_1988_, 2, v_v_2247_);
lean_ctor_set(v___x_1988_, 1, v_k_2246_);
lean_ctor_set(v___x_1988_, 0, v___x_2251_);
v___x_2255_ = v___x_1988_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_2246_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_2247_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_r_2245_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unsigned_to_nat(2u);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 4, v_impl_2131_);
lean_ctor_set(v___x_1988_, 3, v_r_2245_);
lean_ctor_set(v___x_1988_, 0, v___x_2262_);
v___x_2264_ = v___x_1988_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_r_2245_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_impl_2131_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
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
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_k_1979_);
lean_ctor_set(v___x_2268_, 2, v_v_1980_);
lean_ctor_set(v___x_2268_, 3, v_t_1981_);
lean_ctor_set(v___x_2268_, 4, v_t_1981_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v_k_2271_; lean_object* v_v_2272_; lean_object* v_l_2273_; lean_object* v_r_2274_; lean_object* v___x_2275_; 
v_k_2271_ = lean_ctor_get(v_x_2270_, 1);
lean_inc(v_k_2271_);
v_v_2272_ = lean_ctor_get(v_x_2270_, 2);
lean_inc(v_v_2272_);
v_l_2273_ = lean_ctor_get(v_x_2270_, 3);
lean_inc(v_l_2273_);
v_r_2274_ = lean_ctor_get(v_x_2270_, 4);
lean_inc(v_r_2274_);
lean_dec_ref_known(v_x_2270_, 5);
v___x_2275_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2269_, v_l_2273_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_dec(v_r_2274_);
lean_dec(v_v_2272_);
lean_dec(v_k_2271_);
return v___x_2275_;
}
else
{
if (lean_obj_tag(v_v_2272_) == 4)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2390_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2390_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2390_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_elems_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_elems_2280_ = lean_ctor_get(v_v_2272_, 0);
lean_inc_ref(v_elems_2280_);
lean_dec_ref_known(v_v_2272_, 1);
v___x_2281_ = lean_array_get_size(v_elems_2280_);
v___x_2282_ = lean_unsigned_to_nat(8u);
v___x_2283_ = lean_nat_dec_eq(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v___x_2284_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2285_ = l_Nat_reprFast(v___x_2281_);
v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
lean_dec_ref(v___x_2285_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2286_);
v___x_2288_ = v___x_2278_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2278_);
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2291_);
lean_inc(v___x_2292_);
v___x_2293_ = l_Lean_Json_getNat_x3f(v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2302_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2303_);
lean_inc(v___x_2304_);
v___x_2305_ = l_Lean_Json_getNat_x3f(v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_a_2314_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2315_ = lean_unsigned_to_nat(2u);
v___x_2316_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2315_);
lean_inc(v___x_2316_);
v___x_2317_ = l_Lean_Json_getNat_x3f(v___x_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2326_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2327_ = lean_unsigned_to_nat(3u);
v___x_2328_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2327_);
lean_inc(v___x_2328_);
v___x_2329_ = l_Lean_Json_getNat_x3f(v___x_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_a_2326_);
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_a_2338_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2339_ = lean_unsigned_to_nat(4u);
v___x_2340_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2339_);
lean_inc(v___x_2340_);
v___x_2341_ = l_Lean_Json_getNat_x3f(v___x_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2338_);
lean_dec(v_a_2326_);
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2351_ = lean_unsigned_to_nat(5u);
v___x_2352_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2351_);
lean_inc(v___x_2352_);
v___x_2353_ = l_Lean_Json_getNat_x3f(v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2350_);
lean_dec(v_a_2338_);
lean_dec(v_a_2326_);
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2363_ = lean_unsigned_to_nat(6u);
v___x_2364_ = lean_array_get_borrowed(v___x_2290_, v_elems_2280_, v___x_2363_);
lean_inc(v___x_2364_);
v___x_2365_ = l_Lean_Json_getNat_x3f(v___x_2364_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2362_);
lean_dec(v_a_2350_);
lean_dec(v_a_2338_);
lean_dec(v_a_2326_);
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec_ref(v_elems_2280_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2374_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2375_ = lean_unsigned_to_nat(7u);
v___x_2376_ = lean_array_get(v___x_2290_, v_elems_2280_, v___x_2375_);
lean_dec_ref(v_elems_2280_);
v___x_2377_ = l_Lean_Json_getNat_x3f(v___x_2376_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_a_2374_);
lean_dec(v_a_2362_);
lean_dec(v_a_2350_);
lean_dec(v_a_2338_);
lean_dec(v_a_2326_);
lean_dec(v_a_2314_);
lean_dec(v_a_2302_);
lean_dec(v_a_2276_);
lean_dec(v_r_2274_);
lean_dec(v_k_2271_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2386_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2387_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2387_, 0, v_a_2302_);
lean_ctor_set(v___x_2387_, 1, v_a_2314_);
lean_ctor_set(v___x_2387_, 2, v_a_2326_);
lean_ctor_set(v___x_2387_, 3, v_a_2338_);
lean_ctor_set(v___x_2387_, 4, v_a_2350_);
lean_ctor_set(v___x_2387_, 5, v_a_2362_);
lean_ctor_set(v___x_2387_, 6, v_a_2374_);
lean_ctor_set(v___x_2387_, 7, v_a_2386_);
v___x_2388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2271_, v___x_2387_, v_a_2276_);
v_init_2269_ = v___x_2388_;
v_x_2270_ = v_r_2274_;
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
lean_object* v___x_2391_; 
lean_dec_ref_known(v___x_2275_, 1);
lean_dec(v_r_2274_);
lean_dec(v_v_2272_);
lean_dec(v_k_2271_);
v___x_2391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2391_;
}
}
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_init_2269_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2393_, lean_object* v_k_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = l_Lean_Json_getObjValD(v_j_2393_, v_k_2394_);
v___x_2396_ = l_Lean_Json_getObj_x3f(v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_a_2405_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2406_ = lean_box(1);
v___x_2407_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2406_, v_a_2405_);
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2408_, lean_object* v_k_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2408_, v_k_2409_);
lean_dec_ref(v_k_2409_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2411_, size_t v_i_2412_, lean_object* v_bs_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_usize_dec_lt(v_i_2412_, v_sz_2411_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_bs_2413_);
return v___x_2415_;
}
else
{
lean_object* v_v_2416_; lean_object* v___x_2417_; lean_object* v_bs_x27_2418_; size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v_v_2416_ = lean_array_uget(v_bs_2413_, v_i_2412_);
v___x_2417_ = lean_unsigned_to_nat(0u);
v_bs_x27_2418_ = lean_array_uset(v_bs_2413_, v_i_2412_, v___x_2417_);
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = lean_usize_add(v_i_2412_, v___x_2419_);
v___x_2421_ = lean_array_uset(v_bs_x27_2418_, v_i_2412_, v_v_2416_);
v_i_2412_ = v___x_2420_;
v_bs_2413_ = v___x_2421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2423_, lean_object* v_i_2424_, lean_object* v_bs_2425_){
_start:
{
size_t v_sz_boxed_2426_; size_t v_i_boxed_2427_; lean_object* v_res_2428_; 
v_sz_boxed_2426_ = lean_unbox_usize(v_sz_2423_);
lean_dec(v_sz_2423_);
v_i_boxed_2427_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_res_2428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2426_, v_i_boxed_2427_, v_bs_2425_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 4)
{
lean_object* v_elems_2430_; size_t v_sz_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v_elems_2430_ = lean_ctor_get(v_x_2429_, 0);
lean_inc_ref(v_elems_2430_);
lean_dec_ref_known(v_x_2429_, 1);
v_sz_2431_ = lean_array_size(v_elems_2430_);
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2431_, v___x_2432_, v_elems_2430_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2434_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2435_ = lean_unsigned_to_nat(80u);
v___x_2436_ = l_Lean_Json_pretty(v_x_2429_, v___x_2435_);
v___x_2437_ = lean_string_append(v___x_2434_, v___x_2436_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2439_ = lean_string_append(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2462_; 
v_a_2454_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2456_ = v___x_2445_;
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2445_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2462_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_a_2454_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2458_);
v___x_2460_ = v___x_2456_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2463_, lean_object* v_k_2464_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = l_Lean_Json_getObjValD(v_j_2463_, v_k_2464_);
v___x_2466_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2467_, v_k_2468_);
lean_dec_ref(v_k_2468_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2470_, lean_object* v_v_2471_, lean_object* v_t_2472_){
_start:
{
if (lean_obj_tag(v_t_2472_) == 0)
{
lean_object* v_size_2473_; lean_object* v_k_2474_; lean_object* v_v_2475_; lean_object* v_l_2476_; lean_object* v_r_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2757_; 
v_size_2473_ = lean_ctor_get(v_t_2472_, 0);
v_k_2474_ = lean_ctor_get(v_t_2472_, 1);
v_v_2475_ = lean_ctor_get(v_t_2472_, 2);
v_l_2476_ = lean_ctor_get(v_t_2472_, 3);
v_r_2477_ = lean_ctor_get(v_t_2472_, 4);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_t_2472_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2479_ = v_t_2472_;
v_isShared_2480_ = v_isSharedCheck_2757_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_r_2477_);
lean_inc(v_l_2476_);
lean_inc(v_v_2475_);
lean_inc(v_k_2474_);
lean_inc(v_size_2473_);
lean_dec(v_t_2472_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2757_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
uint8_t v___x_2481_; 
v___x_2481_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2470_, v_k_2474_);
switch(v___x_2481_)
{
case 0:
{
lean_object* v_impl_2482_; lean_object* v___x_2483_; 
lean_dec(v_size_2473_);
v_impl_2482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2470_, v_v_2471_, v_l_2476_);
v___x_2483_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2477_) == 0)
{
lean_object* v_size_2484_; lean_object* v_size_2485_; lean_object* v_k_2486_; lean_object* v_v_2487_; lean_object* v_l_2488_; lean_object* v_r_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_size_2484_ = lean_ctor_get(v_r_2477_, 0);
v_size_2485_ = lean_ctor_get(v_impl_2482_, 0);
lean_inc(v_size_2485_);
v_k_2486_ = lean_ctor_get(v_impl_2482_, 1);
lean_inc(v_k_2486_);
v_v_2487_ = lean_ctor_get(v_impl_2482_, 2);
lean_inc(v_v_2487_);
v_l_2488_ = lean_ctor_get(v_impl_2482_, 3);
lean_inc(v_l_2488_);
v_r_2489_ = lean_ctor_get(v_impl_2482_, 4);
lean_inc(v_r_2489_);
v___x_2490_ = lean_unsigned_to_nat(3u);
v___x_2491_ = lean_nat_mul(v___x_2490_, v_size_2484_);
v___x_2492_ = lean_nat_dec_lt(v___x_2491_, v_size_2485_);
lean_dec(v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec(v_r_2489_);
lean_dec(v_l_2488_);
lean_dec(v_v_2487_);
lean_dec(v_k_2486_);
v___x_2493_ = lean_nat_add(v___x_2483_, v_size_2485_);
lean_dec(v_size_2485_);
v___x_2494_ = lean_nat_add(v___x_2493_, v_size_2484_);
lean_dec(v___x_2493_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 3, v_impl_2482_);
lean_ctor_set(v___x_2479_, 0, v___x_2494_);
v___x_2496_ = v___x_2479_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_impl_2482_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_r_2477_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
else
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2563_; 
v_isSharedCheck_2563_ = !lean_is_exclusive(v_impl_2482_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; lean_object* v_unused_2565_; lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2564_ = lean_ctor_get(v_impl_2482_, 4);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_impl_2482_, 3);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v_impl_2482_, 2);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_impl_2482_, 1);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_impl_2482_, 0);
lean_dec(v_unused_2568_);
v___x_2499_ = v_impl_2482_;
v_isShared_2500_ = v_isSharedCheck_2563_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v_impl_2482_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2563_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_size_2501_; lean_object* v_size_2502_; lean_object* v_k_2503_; lean_object* v_v_2504_; lean_object* v_l_2505_; lean_object* v_r_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v_size_2501_ = lean_ctor_get(v_l_2488_, 0);
v_size_2502_ = lean_ctor_get(v_r_2489_, 0);
v_k_2503_ = lean_ctor_get(v_r_2489_, 1);
v_v_2504_ = lean_ctor_get(v_r_2489_, 2);
v_l_2505_ = lean_ctor_get(v_r_2489_, 3);
v_r_2506_ = lean_ctor_get(v_r_2489_, 4);
v___x_2507_ = lean_unsigned_to_nat(2u);
v___x_2508_ = lean_nat_mul(v___x_2507_, v_size_2501_);
v___x_2509_ = lean_nat_dec_lt(v_size_2502_, v___x_2508_);
lean_dec(v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2538_; 
lean_inc(v_r_2506_);
lean_inc(v_l_2505_);
lean_inc(v_v_2504_);
lean_inc(v_k_2503_);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_r_2489_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2539_ = lean_ctor_get(v_r_2489_, 4);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_r_2489_, 3);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_r_2489_, 2);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_r_2489_, 1);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_r_2489_, 0);
lean_dec(v_unused_2543_);
v___x_2511_ = v_r_2489_;
v_isShared_2512_ = v_isSharedCheck_2538_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v_r_2489_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2538_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___x_2526_; lean_object* v___y_2528_; 
v___x_2513_ = lean_nat_add(v___x_2483_, v_size_2485_);
lean_dec(v_size_2485_);
v___x_2514_ = lean_nat_add(v___x_2513_, v_size_2484_);
lean_dec(v___x_2513_);
v___x_2526_ = lean_nat_add(v___x_2483_, v_size_2501_);
if (lean_obj_tag(v_l_2505_) == 0)
{
lean_object* v_size_2536_; 
v_size_2536_ = lean_ctor_get(v_l_2505_, 0);
lean_inc(v_size_2536_);
v___y_2528_ = v_size_2536_;
goto v___jp_2527_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_unsigned_to_nat(0u);
v___y_2528_ = v___x_2537_;
goto v___jp_2527_;
}
v___jp_2515_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = lean_nat_add(v___y_2516_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec(v___y_2516_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v_r_2477_);
lean_ctor_set(v___x_2511_, 3, v_r_2506_);
lean_ctor_set(v___x_2511_, 2, v_v_2475_);
lean_ctor_set(v___x_2511_, 1, v_k_2474_);
lean_ctor_set(v___x_2511_, 0, v___x_2519_);
v___x_2521_ = v___x_2511_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_r_2506_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_r_2477_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 4, v___x_2521_);
lean_ctor_set(v___x_2499_, 3, v___y_2517_);
lean_ctor_set(v___x_2499_, 2, v_v_2504_);
lean_ctor_set(v___x_2499_, 1, v_k_2503_);
lean_ctor_set(v___x_2499_, 0, v___x_2514_);
v___x_2523_ = v___x_2499_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_2503_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_2504_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___y_2517_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_nat_add(v___x_2526_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec(v___x_2526_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_l_2505_);
lean_ctor_set(v___x_2479_, 3, v_l_2488_);
lean_ctor_set(v___x_2479_, 2, v_v_2487_);
lean_ctor_set(v___x_2479_, 1, v_k_2486_);
lean_ctor_set(v___x_2479_, 0, v___x_2529_);
v___x_2531_ = v___x_2479_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2486_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2487_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_l_2488_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_l_2505_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_nat_add(v___x_2483_, v_size_2484_);
if (lean_obj_tag(v_r_2506_) == 0)
{
lean_object* v_size_2533_; 
v_size_2533_ = lean_ctor_get(v_r_2506_, 0);
lean_inc(v_size_2533_);
v___y_2516_ = v___x_2532_;
v___y_2517_ = v___x_2531_;
v___y_2518_ = v_size_2533_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v___y_2516_ = v___x_2532_;
v___y_2517_ = v___x_2531_;
v___y_2518_ = v___x_2534_;
goto v___jp_2515_;
}
}
}
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_del_object(v___x_2479_);
v___x_2544_ = lean_nat_add(v___x_2483_, v_size_2485_);
lean_dec(v_size_2485_);
v___x_2545_ = lean_nat_add(v___x_2544_, v_size_2484_);
lean_dec(v___x_2544_);
v___x_2546_ = lean_nat_add(v___x_2483_, v_size_2484_);
v___x_2547_ = lean_nat_add(v___x_2546_, v_size_2502_);
lean_dec(v___x_2546_);
lean_inc_ref(v_r_2477_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 4, v_r_2477_);
lean_ctor_set(v___x_2499_, 3, v_r_2489_);
lean_ctor_set(v___x_2499_, 2, v_v_2475_);
lean_ctor_set(v___x_2499_, 1, v_k_2474_);
lean_ctor_set(v___x_2499_, 0, v___x_2547_);
v___x_2549_ = v___x_2499_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_r_2489_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_r_2477_);
v___x_2549_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v_r_2477_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; lean_object* v_unused_2561_; 
v_unused_2557_ = lean_ctor_get(v_r_2477_, 4);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_r_2477_, 3);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_r_2477_, 2);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_r_2477_, 1);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_r_2477_, 0);
lean_dec(v_unused_2561_);
v___x_2551_ = v_r_2477_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_dec(v_r_2477_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v___x_2549_);
lean_ctor_set(v___x_2551_, 3, v_l_2488_);
lean_ctor_set(v___x_2551_, 2, v_v_2487_);
lean_ctor_set(v___x_2551_, 1, v_k_2486_);
lean_ctor_set(v___x_2551_, 0, v___x_2545_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_k_2486_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_v_2487_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_l_2488_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v___x_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2569_; 
v_l_2569_ = lean_ctor_get(v_impl_2482_, 3);
lean_inc(v_l_2569_);
if (lean_obj_tag(v_l_2569_) == 0)
{
lean_object* v_r_2570_; lean_object* v_k_2571_; lean_object* v_v_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2583_; 
v_r_2570_ = lean_ctor_get(v_impl_2482_, 4);
v_k_2571_ = lean_ctor_get(v_impl_2482_, 1);
v_v_2572_ = lean_ctor_get(v_impl_2482_, 2);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_impl_2482_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2584_ = lean_ctor_get(v_impl_2482_, 3);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_impl_2482_, 0);
lean_dec(v_unused_2585_);
v___x_2574_ = v_impl_2482_;
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_r_2570_);
lean_inc(v_v_2572_);
lean_inc(v_k_2571_);
lean_dec(v_impl_2482_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2570_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 3, v_r_2570_);
lean_ctor_set(v___x_2574_, 2, v_v_2475_);
lean_ctor_set(v___x_2574_, 1, v_k_2474_);
lean_ctor_set(v___x_2574_, 0, v___x_2483_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_r_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_r_2570_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v___x_2578_);
lean_ctor_set(v___x_2479_, 3, v_l_2569_);
lean_ctor_set(v___x_2479_, 2, v_v_2572_);
lean_ctor_set(v___x_2479_, 1, v_k_2571_);
lean_ctor_set(v___x_2479_, 0, v___x_2576_);
v___x_2580_ = v___x_2479_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2571_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2572_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_l_2569_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_r_2586_; 
v_r_2586_ = lean_ctor_get(v_impl_2482_, 4);
lean_inc(v_r_2586_);
if (lean_obj_tag(v_r_2586_) == 0)
{
lean_object* v_k_2587_; lean_object* v_v_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2611_; 
v_k_2587_ = lean_ctor_get(v_impl_2482_, 1);
v_v_2588_ = lean_ctor_get(v_impl_2482_, 2);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_impl_2482_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; lean_object* v_unused_2613_; lean_object* v_unused_2614_; 
v_unused_2612_ = lean_ctor_get(v_impl_2482_, 4);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_impl_2482_, 3);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v_impl_2482_, 0);
lean_dec(v_unused_2614_);
v___x_2590_ = v_impl_2482_;
v_isShared_2591_ = v_isSharedCheck_2611_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_v_2588_);
lean_inc(v_k_2587_);
lean_dec(v_impl_2482_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2611_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_k_2592_; lean_object* v_v_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2607_; 
v_k_2592_ = lean_ctor_get(v_r_2586_, 1);
v_v_2593_ = lean_ctor_get(v_r_2586_, 2);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_r_2586_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; lean_object* v_unused_2609_; lean_object* v_unused_2610_; 
v_unused_2608_ = lean_ctor_get(v_r_2586_, 4);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_r_2586_, 3);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_r_2586_, 0);
lean_dec(v_unused_2610_);
v___x_2595_ = v_r_2586_;
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_v_2593_);
lean_inc(v_k_2592_);
lean_dec(v_r_2586_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_unsigned_to_nat(3u);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 4, v_l_2569_);
lean_ctor_set(v___x_2595_, 3, v_l_2569_);
lean_ctor_set(v___x_2595_, 2, v_v_2588_);
lean_ctor_set(v___x_2595_, 1, v_k_2587_);
lean_ctor_set(v___x_2595_, 0, v___x_2483_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_l_2569_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_l_2569_);
v___x_2599_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2601_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 4, v_l_2569_);
lean_ctor_set(v___x_2590_, 2, v_v_2475_);
lean_ctor_set(v___x_2590_, 1, v_k_2474_);
lean_ctor_set(v___x_2590_, 0, v___x_2483_);
v___x_2601_ = v___x_2590_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_l_2569_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_l_2569_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v___x_2601_);
lean_ctor_set(v___x_2479_, 3, v___x_2599_);
lean_ctor_set(v___x_2479_, 2, v_v_2593_);
lean_ctor_set(v___x_2479_, 1, v_k_2592_);
lean_ctor_set(v___x_2479_, 0, v___x_2597_);
v___x_2603_ = v___x_2479_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2592_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2593_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v___x_2601_);
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
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_unsigned_to_nat(2u);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_r_2586_);
lean_ctor_set(v___x_2479_, 3, v_impl_2482_);
lean_ctor_set(v___x_2479_, 0, v___x_2615_);
v___x_2617_ = v___x_2479_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_impl_2482_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_r_2586_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2620_; 
lean_dec(v_v_2475_);
lean_dec(v_k_2474_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 2, v_v_2471_);
lean_ctor_set(v___x_2479_, 1, v_k_2470_);
v___x_2620_ = v___x_2479_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_2473_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2470_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2471_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_l_2476_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_r_2477_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
default: 
{
lean_object* v_impl_2622_; lean_object* v___x_2623_; 
lean_dec(v_size_2473_);
v_impl_2622_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2470_, v_v_2471_, v_r_2477_);
v___x_2623_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2476_) == 0)
{
lean_object* v_size_2624_; lean_object* v_size_2625_; lean_object* v_k_2626_; lean_object* v_v_2627_; lean_object* v_l_2628_; lean_object* v_r_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_size_2624_ = lean_ctor_get(v_l_2476_, 0);
v_size_2625_ = lean_ctor_get(v_impl_2622_, 0);
lean_inc(v_size_2625_);
v_k_2626_ = lean_ctor_get(v_impl_2622_, 1);
lean_inc(v_k_2626_);
v_v_2627_ = lean_ctor_get(v_impl_2622_, 2);
lean_inc(v_v_2627_);
v_l_2628_ = lean_ctor_get(v_impl_2622_, 3);
lean_inc(v_l_2628_);
v_r_2629_ = lean_ctor_get(v_impl_2622_, 4);
lean_inc(v_r_2629_);
v___x_2630_ = lean_unsigned_to_nat(3u);
v___x_2631_ = lean_nat_mul(v___x_2630_, v_size_2624_);
v___x_2632_ = lean_nat_dec_lt(v___x_2631_, v_size_2625_);
lean_dec(v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
lean_dec(v_r_2629_);
lean_dec(v_l_2628_);
lean_dec(v_v_2627_);
lean_dec(v_k_2626_);
v___x_2633_ = lean_nat_add(v___x_2623_, v_size_2624_);
v___x_2634_ = lean_nat_add(v___x_2633_, v_size_2625_);
lean_dec(v_size_2625_);
lean_dec(v___x_2633_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_impl_2622_);
lean_ctor_set(v___x_2479_, 0, v___x_2634_);
v___x_2636_ = v___x_2479_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_l_2476_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_impl_2622_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2701_; 
v_isSharedCheck_2701_ = !lean_is_exclusive(v_impl_2622_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2702_ = lean_ctor_get(v_impl_2622_, 4);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_impl_2622_, 3);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_impl_2622_, 2);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_impl_2622_, 1);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_impl_2622_, 0);
lean_dec(v_unused_2706_);
v___x_2639_ = v_impl_2622_;
v_isShared_2640_ = v_isSharedCheck_2701_;
goto v_resetjp_2638_;
}
else
{
lean_dec(v_impl_2622_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2701_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_size_2641_; lean_object* v_k_2642_; lean_object* v_v_2643_; lean_object* v_l_2644_; lean_object* v_r_2645_; lean_object* v_size_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_size_2641_ = lean_ctor_get(v_l_2628_, 0);
v_k_2642_ = lean_ctor_get(v_l_2628_, 1);
v_v_2643_ = lean_ctor_get(v_l_2628_, 2);
v_l_2644_ = lean_ctor_get(v_l_2628_, 3);
v_r_2645_ = lean_ctor_get(v_l_2628_, 4);
v_size_2646_ = lean_ctor_get(v_r_2629_, 0);
v___x_2647_ = lean_unsigned_to_nat(2u);
v___x_2648_ = lean_nat_mul(v___x_2647_, v_size_2646_);
v___x_2649_ = lean_nat_dec_lt(v_size_2641_, v___x_2648_);
lean_dec(v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2677_; 
lean_inc(v_r_2645_);
lean_inc(v_l_2644_);
lean_inc(v_v_2643_);
lean_inc(v_k_2642_);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_l_2628_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2678_ = lean_ctor_get(v_l_2628_, 4);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2628_, 3);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2628_, 2);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2628_, 1);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_l_2628_, 0);
lean_dec(v_unused_2682_);
v___x_2651_ = v_l_2628_;
v_isShared_2652_ = v_isSharedCheck_2677_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v_l_2628_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2677_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2667_; 
v___x_2653_ = lean_nat_add(v___x_2623_, v_size_2624_);
v___x_2654_ = lean_nat_add(v___x_2653_, v_size_2625_);
lean_dec(v_size_2625_);
if (lean_obj_tag(v_l_2644_) == 0)
{
lean_object* v_size_2675_; 
v_size_2675_ = lean_ctor_get(v_l_2644_, 0);
lean_inc(v_size_2675_);
v___y_2667_ = v_size_2675_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_unsigned_to_nat(0u);
v___y_2667_ = v___x_2676_;
goto v___jp_2666_;
}
v___jp_2655_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = lean_nat_add(v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec(v___y_2657_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 4, v_r_2629_);
lean_ctor_set(v___x_2651_, 3, v_r_2645_);
lean_ctor_set(v___x_2651_, 2, v_v_2627_);
lean_ctor_set(v___x_2651_, 1, v_k_2626_);
lean_ctor_set(v___x_2651_, 0, v___x_2659_);
v___x_2661_ = v___x_2651_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v_r_2645_);
lean_ctor_set(v_reuseFailAlloc_2665_, 4, v_r_2629_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 4, v___x_2661_);
lean_ctor_set(v___x_2639_, 3, v___y_2656_);
lean_ctor_set(v___x_2639_, 2, v_v_2643_);
lean_ctor_set(v___x_2639_, 1, v_k_2642_);
lean_ctor_set(v___x_2639_, 0, v___x_2654_);
v___x_2663_ = v___x_2639_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_k_2642_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_v_2643_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v___y_2656_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_nat_add(v___x_2653_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec(v___x_2653_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_l_2644_);
lean_ctor_set(v___x_2479_, 0, v___x_2668_);
v___x_2670_ = v___x_2479_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_l_2476_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_l_2644_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_nat_add(v___x_2623_, v_size_2646_);
if (lean_obj_tag(v_r_2645_) == 0)
{
lean_object* v_size_2672_; 
v_size_2672_ = lean_ctor_get(v_r_2645_, 0);
lean_inc(v_size_2672_);
v___y_2656_ = v___x_2670_;
v___y_2657_ = v___x_2671_;
v___y_2658_ = v_size_2672_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___y_2656_ = v___x_2670_;
v___y_2657_ = v___x_2671_;
v___y_2658_ = v___x_2673_;
goto v___jp_2655_;
}
}
}
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_del_object(v___x_2479_);
v___x_2683_ = lean_nat_add(v___x_2623_, v_size_2624_);
v___x_2684_ = lean_nat_add(v___x_2683_, v_size_2625_);
lean_dec(v_size_2625_);
v___x_2685_ = lean_nat_add(v___x_2683_, v_size_2641_);
lean_dec(v___x_2683_);
lean_inc_ref(v_l_2476_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 4, v_l_2628_);
lean_ctor_set(v___x_2639_, 3, v_l_2476_);
lean_ctor_set(v___x_2639_, 2, v_v_2475_);
lean_ctor_set(v___x_2639_, 1, v_k_2474_);
lean_ctor_set(v___x_2639_, 0, v___x_2685_);
v___x_2687_ = v___x_2639_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_l_2476_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_l_2628_);
v___x_2687_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_isSharedCheck_2694_ = !lean_is_exclusive(v_l_2476_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2695_ = lean_ctor_get(v_l_2476_, 4);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_l_2476_, 3);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_l_2476_, 2);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_l_2476_, 1);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_l_2476_, 0);
lean_dec(v_unused_2699_);
v___x_2689_ = v_l_2476_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v_l_2476_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 4, v_r_2629_);
lean_ctor_set(v___x_2689_, 3, v___x_2687_);
lean_ctor_set(v___x_2689_, 2, v_v_2627_);
lean_ctor_set(v___x_2689_, 1, v_k_2626_);
lean_ctor_set(v___x_2689_, 0, v___x_2684_);
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2693_, 4, v_r_2629_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2707_; 
v_l_2707_ = lean_ctor_get(v_impl_2622_, 3);
lean_inc(v_l_2707_);
if (lean_obj_tag(v_l_2707_) == 0)
{
lean_object* v_r_2708_; lean_object* v_k_2709_; lean_object* v_v_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2733_; 
v_r_2708_ = lean_ctor_get(v_impl_2622_, 4);
v_k_2709_ = lean_ctor_get(v_impl_2622_, 1);
v_v_2710_ = lean_ctor_get(v_impl_2622_, 2);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_impl_2622_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2734_ = lean_ctor_get(v_impl_2622_, 3);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_impl_2622_, 0);
lean_dec(v_unused_2735_);
v___x_2712_ = v_impl_2622_;
v_isShared_2713_ = v_isSharedCheck_2733_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_r_2708_);
lean_inc(v_v_2710_);
lean_inc(v_k_2709_);
lean_dec(v_impl_2622_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2733_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_k_2714_; lean_object* v_v_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2729_; 
v_k_2714_ = lean_ctor_get(v_l_2707_, 1);
v_v_2715_ = lean_ctor_get(v_l_2707_, 2);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_l_2707_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2730_ = lean_ctor_get(v_l_2707_, 4);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_l_2707_, 3);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_l_2707_, 0);
lean_dec(v_unused_2732_);
v___x_2717_ = v_l_2707_;
v_isShared_2718_ = v_isSharedCheck_2729_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_v_2715_);
lean_inc(v_k_2714_);
lean_dec(v_l_2707_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2729_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2719_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2708_, 2);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 4, v_r_2708_);
lean_ctor_set(v___x_2717_, 3, v_r_2708_);
lean_ctor_set(v___x_2717_, 2, v_v_2475_);
lean_ctor_set(v___x_2717_, 1, v_k_2474_);
lean_ctor_set(v___x_2717_, 0, v___x_2623_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_r_2708_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_r_2708_);
v___x_2721_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2723_; 
lean_inc(v_r_2708_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 3, v_r_2708_);
lean_ctor_set(v___x_2712_, 0, v___x_2623_);
v___x_2723_ = v___x_2712_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_k_2709_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_v_2710_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v_r_2708_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_r_2708_);
v___x_2723_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v___x_2723_);
lean_ctor_set(v___x_2479_, 3, v___x_2721_);
lean_ctor_set(v___x_2479_, 2, v_v_2715_);
lean_ctor_set(v___x_2479_, 1, v_k_2714_);
lean_ctor_set(v___x_2479_, 0, v___x_2719_);
v___x_2725_ = v___x_2479_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2714_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2715_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
else
{
lean_object* v_r_2736_; 
v_r_2736_ = lean_ctor_get(v_impl_2622_, 4);
lean_inc(v_r_2736_);
if (lean_obj_tag(v_r_2736_) == 0)
{
lean_object* v_k_2737_; lean_object* v_v_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2749_; 
v_k_2737_ = lean_ctor_get(v_impl_2622_, 1);
v_v_2738_ = lean_ctor_get(v_impl_2622_, 2);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_impl_2622_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2750_ = lean_ctor_get(v_impl_2622_, 4);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_impl_2622_, 3);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_impl_2622_, 0);
lean_dec(v_unused_2752_);
v___x_2740_ = v_impl_2622_;
v_isShared_2741_ = v_isSharedCheck_2749_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_v_2738_);
lean_inc(v_k_2737_);
lean_dec(v_impl_2622_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2749_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = lean_unsigned_to_nat(3u);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v_l_2707_);
lean_ctor_set(v___x_2740_, 2, v_v_2475_);
lean_ctor_set(v___x_2740_, 1, v_k_2474_);
lean_ctor_set(v___x_2740_, 0, v___x_2623_);
v___x_2744_ = v___x_2740_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_l_2707_);
lean_ctor_set(v_reuseFailAlloc_2748_, 4, v_l_2707_);
v___x_2744_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2746_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_r_2736_);
lean_ctor_set(v___x_2479_, 3, v___x_2744_);
lean_ctor_set(v___x_2479_, 2, v_v_2738_);
lean_ctor_set(v___x_2479_, 1, v_k_2737_);
lean_ctor_set(v___x_2479_, 0, v___x_2742_);
v___x_2746_ = v___x_2479_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_k_2737_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_v_2738_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_r_2736_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2753_ = lean_unsigned_to_nat(2u);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 4, v_impl_2622_);
lean_ctor_set(v___x_2479_, 3, v_r_2736_);
lean_ctor_set(v___x_2479_, 0, v___x_2753_);
v___x_2755_ = v___x_2479_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_k_2474_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_v_2475_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_r_2736_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_impl_2622_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
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
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_unsigned_to_nat(1u);
v___x_2759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_k_2470_);
lean_ctor_set(v___x_2759_, 2, v_v_2471_);
lean_ctor_set(v___x_2759_, 3, v_t_2472_);
lean_ctor_set(v___x_2759_, 4, v_t_2472_);
return v___x_2759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2760_, size_t v_i_2761_, lean_object* v_bs_2762_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2761_, v_sz_2760_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_bs_2762_);
return v___x_2764_;
}
else
{
lean_object* v_v_2765_; lean_object* v___x_2766_; lean_object* v_bs_x27_2767_; lean_object* v_a_2769_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___y_2777_; uint8_t v___y_2841_; uint8_t v___y_2842_; uint8_t v___y_2843_; uint8_t v___y_2849_; uint8_t v___x_2853_; 
v_v_2765_ = lean_array_uget(v_bs_2762_, v_i_2761_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v_bs_x27_2767_ = lean_array_uset(v_bs_2762_, v_i_2761_, v___x_2766_);
v___x_2774_ = lean_array_get_size(v_v_2765_);
v___x_2775_ = lean_unsigned_to_nat(4u);
v___x_2853_ = lean_nat_dec_eq(v___x_2774_, v___x_2775_);
if (v___x_2853_ == 0)
{
v___y_2849_ = v___x_2763_;
goto v___jp_2848_;
}
else
{
uint8_t v___x_2854_; 
v___x_2854_ = 0;
v___y_2849_ = v___x_2854_;
goto v___jp_2848_;
}
v___jp_2768_:
{
size_t v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((size_t)1ULL);
v___x_2771_ = lean_usize_add(v_i_2761_, v___x_2770_);
v___x_2772_ = lean_array_uset(v_bs_x27_2767_, v_i_2761_, v_a_2769_);
v_i_2761_ = v___x_2771_;
v_bs_2762_ = v___x_2772_;
goto _start;
}
v___jp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_array_fget_borrowed(v_v_2765_, v___x_2766_);
lean_inc(v___x_2778_);
v___x_2779_ = l_Lean_Json_getNat_x3f(v___x_2778_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_a_2788_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_array_fget_borrowed(v_v_2765_, v___x_2789_);
lean_inc(v___x_2790_);
v___x_2791_ = l_Lean_Json_getNat_x3f(v___x_2790_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2788_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
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
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_a_2800_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2801_ = lean_unsigned_to_nat(2u);
v___x_2802_ = lean_array_fget_borrowed(v_v_2765_, v___x_2801_);
lean_inc(v___x_2802_);
v___x_2803_ = l_Lean_Json_getNat_x3f(v___x_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2800_);
lean_dec(v_a_2788_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2812_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2813_ = lean_unsigned_to_nat(3u);
v___x_2814_ = lean_array_fget_borrowed(v_v_2765_, v___x_2813_);
lean_inc(v___x_2814_);
v___x_2815_ = l_Lean_Json_getNat_x3f(v___x_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2800_);
lean_dec(v_a_2788_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
if (v___y_2777_ == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v_v_2765_);
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2825_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2788_);
lean_ctor_set(v___x_2826_, 1, v_a_2800_);
lean_ctor_set(v___x_2826_, 2, v_a_2812_);
lean_ctor_set(v___x_2826_, 3, v_a_2824_);
lean_ctor_set(v___x_2826_, 4, v___x_2825_);
v_a_2769_ = v___x_2826_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2827_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2828_ = lean_array_fget(v_v_2765_, v___x_2775_);
lean_dec(v_v_2765_);
v___x_2829_ = l_Lean_Json_getStr_x3f(v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2827_);
lean_dec(v_a_2812_);
lean_dec(v_a_2800_);
lean_dec(v_a_2788_);
lean_dec_ref(v_bs_x27_2767_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2839_; 
v_a_2838_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2788_);
lean_ctor_set(v___x_2839_, 1, v_a_2800_);
lean_ctor_set(v___x_2839_, 2, v_a_2812_);
lean_ctor_set(v___x_2839_, 3, v_a_2827_);
lean_ctor_set(v___x_2839_, 4, v_a_2838_);
v_a_2769_ = v___x_2839_;
goto v___jp_2768_;
}
}
}
}
}
}
}
v___jp_2840_:
{
if (v___y_2841_ == 0)
{
v___y_2777_ = v___y_2842_;
goto v___jp_2776_;
}
else
{
if (v___y_2843_ == 0)
{
v___y_2777_ = v___y_2842_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v___x_2844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2845_ = l_Nat_reprFast(v___x_2774_);
v___x_2846_ = lean_string_append(v___x_2844_, v___x_2845_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
}
v___jp_2848_:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = lean_unsigned_to_nat(5u);
v___x_2851_ = lean_nat_dec_eq(v___x_2774_, v___x_2850_);
if (v___x_2851_ == 0)
{
v___y_2841_ = v___y_2849_;
v___y_2842_ = v___x_2851_;
v___y_2843_ = v___x_2763_;
goto v___jp_2840_;
}
else
{
uint8_t v___x_2852_; 
v___x_2852_ = 0;
v___y_2841_ = v___y_2849_;
v___y_2842_ = v___x_2851_;
v___y_2843_ = v___x_2852_;
goto v___jp_2840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2855_, lean_object* v_i_2856_, lean_object* v_bs_2857_){
_start:
{
size_t v_sz_boxed_2858_; size_t v_i_boxed_2859_; lean_object* v_res_2860_; 
v_sz_boxed_2858_ = lean_unbox_usize(v_sz_2855_);
lean_dec(v_sz_2855_);
v_i_boxed_2859_ = lean_unbox_usize(v_i_2856_);
lean_dec(v_i_2856_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2858_, v_i_boxed_2859_, v_bs_2857_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_bs_2863_){
_start:
{
uint8_t v___x_2864_; 
v___x_2864_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_bs_2863_);
return v___x_2865_;
}
else
{
lean_object* v_v_2866_; lean_object* v___x_2867_; 
v_v_2866_ = lean_array_uget_borrowed(v_bs_2863_, v_i_2862_);
lean_inc(v_v_2866_);
v___x_2867_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_bs_2863_);
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v_bs_x27_2878_; size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
v_a_2876_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2877_ = lean_unsigned_to_nat(0u);
v_bs_x27_2878_ = lean_array_uset(v_bs_2863_, v_i_2862_, v___x_2877_);
v___x_2879_ = ((size_t)1ULL);
v___x_2880_ = lean_usize_add(v_i_2862_, v___x_2879_);
v___x_2881_ = lean_array_uset(v_bs_x27_2878_, v_i_2862_, v_a_2876_);
v_i_2862_ = v___x_2880_;
v_bs_2863_ = v___x_2881_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2883_, lean_object* v_i_2884_, lean_object* v_bs_2885_){
_start:
{
size_t v_sz_boxed_2886_; size_t v_i_boxed_2887_; lean_object* v_res_2888_; 
v_sz_boxed_2886_ = lean_unbox_usize(v_sz_2883_);
lean_dec(v_sz_2883_);
v_i_boxed_2887_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2886_, v_i_boxed_2887_, v_bs_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 4)
{
lean_object* v_elems_2890_; size_t v_sz_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
v_elems_2890_ = lean_ctor_get(v_x_2889_, 0);
lean_inc_ref(v_elems_2890_);
lean_dec_ref_known(v_x_2889_, 1);
v_sz_2891_ = lean_array_size(v_elems_2890_);
v___x_2892_ = ((size_t)0ULL);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2891_, v___x_2892_, v_elems_2890_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2894_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2895_ = lean_unsigned_to_nat(80u);
v___x_2896_ = l_Lean_Json_pretty(v_x_2889_, v___x_2895_);
v___x_2897_ = lean_string_append(v___x_2894_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2899_ = lean_string_append(v___x_2897_, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2901_, lean_object* v_k_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = l_Lean_Json_getObjValD(v_j_2901_, v_k_2902_);
v___x_2904_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2905_, lean_object* v_k_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2905_, v_k_2906_);
lean_dec_ref(v_k_2906_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2908_, lean_object* v_x_2909_){
_start:
{
if (lean_obj_tag(v_x_2909_) == 0)
{
lean_object* v_k_2910_; lean_object* v_v_2911_; lean_object* v_l_2912_; lean_object* v_r_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3083_; 
v_k_2910_ = lean_ctor_get(v_x_2909_, 1);
v_v_2911_ = lean_ctor_get(v_x_2909_, 2);
v_l_2912_ = lean_ctor_get(v_x_2909_, 3);
v_r_2913_ = lean_ctor_get(v_x_2909_, 4);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_x_2909_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v_x_2909_, 0);
lean_dec(v_unused_3084_);
v___x_2915_ = v_x_2909_;
v_isShared_2916_ = v_isSharedCheck_3083_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_r_2913_);
lean_inc(v_l_2912_);
lean_inc(v_v_2911_);
lean_inc(v_k_2910_);
lean_dec(v_x_2909_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3083_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2908_, v_l_2912_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
lean_dec(v_k_2910_);
return v___x_2917_;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_3082_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_3082_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_3082_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Json_parse(v_k_2910_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2932_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v_definition_x3f_2943_; lean_object* v_a_2971_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_a_2941_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2975_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2911_);
v___x_2976_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2911_, v___x_2975_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2976_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
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
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3081_; 
v_a_2985_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_2987_ = v___x_2976_;
v_isShared_2988_ = v_isSharedCheck_3081_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2976_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3081_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
if (lean_obj_tag(v_a_2985_) == 0)
{
lean_object* v___x_2989_; 
lean_del_object(v___x_2987_);
lean_del_object(v___x_2920_);
lean_del_object(v___x_2915_);
v___x_2989_ = lean_box(0);
v_definition_x3f_2943_ = v___x_2989_;
goto v___jp_2942_;
}
else
{
lean_object* v_val_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___y_2994_; uint8_t v___y_3063_; uint8_t v___y_3064_; uint8_t v___y_3065_; uint8_t v___y_3073_; uint8_t v___x_3078_; 
v_val_2990_ = lean_ctor_get(v_a_2985_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v_a_2985_, 1);
v___x_2991_ = lean_array_get_size(v_val_2990_);
v___x_2992_ = lean_unsigned_to_nat(4u);
v___x_3078_ = lean_nat_dec_eq(v___x_2991_, v___x_2992_);
if (v___x_3078_ == 0)
{
uint8_t v___x_3079_; 
v___x_3079_ = 1;
v___y_3073_ = v___x_3079_;
goto v___jp_3072_;
}
else
{
uint8_t v___x_3080_; 
v___x_3080_ = 0;
v___y_3073_ = v___x_3080_;
goto v___jp_3072_;
}
v___jp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_unsigned_to_nat(0u);
v___x_2996_ = lean_array_fget_borrowed(v_val_2990_, v___x_2995_);
lean_inc(v___x_2996_);
v___x_2997_ = l_Lean_Json_getNat_x3f(v___x_2996_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_val_2990_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3006_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_array_fget_borrowed(v_val_2990_, v___x_3007_);
lean_inc(v___x_3008_);
v___x_3009_ = l_Lean_Json_getNat_x3f(v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_3006_);
lean_dec(v_val_2990_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3018_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3019_ = lean_unsigned_to_nat(2u);
v___x_3020_ = lean_array_fget_borrowed(v_val_2990_, v___x_3019_);
lean_inc(v___x_3020_);
v___x_3021_ = l_Lean_Json_getNat_x3f(v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_3018_);
lean_dec(v_a_3006_);
lean_dec(v_val_2990_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
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
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_a_3030_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3031_ = lean_unsigned_to_nat(3u);
v___x_3032_ = lean_array_fget_borrowed(v_val_2990_, v___x_3031_);
lean_inc(v___x_3032_);
v___x_3033_ = l_Lean_Json_getNat_x3f(v___x_3032_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_3030_);
lean_dec(v_a_3018_);
lean_dec(v_a_3006_);
lean_dec(v_val_2990_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
if (v___y_2994_ == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_dec(v_val_2990_);
v_a_3042_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3043_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 4, v___x_3043_);
lean_ctor_set(v___x_2915_, 3, v_a_3042_);
lean_ctor_set(v___x_2915_, 2, v_a_3030_);
lean_ctor_set(v___x_2915_, 1, v_a_3018_);
lean_ctor_set(v___x_2915_, 0, v_a_3006_);
v___x_3045_ = v___x_2915_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3006_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_a_3042_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
v_a_2971_ = v___x_3045_;
goto v___jp_2970_;
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v_a_3047_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3048_ = lean_array_fget(v_val_2990_, v___x_2992_);
lean_dec(v_val_2990_);
v___x_3049_ = l_Lean_Json_getStr_x3f(v___x_3048_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_3047_);
lean_dec(v_a_3030_);
lean_dec(v_a_3018_);
lean_dec(v_a_3006_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3049_, 1);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 4, v_a_3058_);
lean_ctor_set(v___x_2915_, 3, v_a_3047_);
lean_ctor_set(v___x_2915_, 2, v_a_3030_);
lean_ctor_set(v___x_2915_, 1, v_a_3018_);
lean_ctor_set(v___x_2915_, 0, v_a_3006_);
v___x_3060_ = v___x_2915_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3006_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v_a_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
v_a_2971_ = v___x_3060_;
goto v___jp_2970_;
}
}
}
}
}
}
}
}
v___jp_3062_:
{
if (v___y_3064_ == 0)
{
lean_del_object(v___x_2987_);
v___y_2994_ = v___y_3063_;
goto v___jp_2993_;
}
else
{
if (v___y_3065_ == 0)
{
lean_del_object(v___x_2987_);
v___y_2994_ = v___y_3063_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_dec(v_val_2990_);
lean_dec(v_a_2941_);
lean_del_object(v___x_2920_);
lean_dec(v_a_2918_);
lean_del_object(v___x_2915_);
lean_dec(v_r_2913_);
lean_dec(v_v_2911_);
v___x_3066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3067_ = l_Nat_reprFast(v___x_2991_);
v___x_3068_ = lean_string_append(v___x_3066_, v___x_3067_);
lean_dec_ref(v___x_3067_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 0);
lean_ctor_set(v___x_2987_, 0, v___x_3068_);
v___x_3070_ = v___x_2987_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
v___jp_3072_:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = lean_unsigned_to_nat(5u);
v___x_3075_ = lean_nat_dec_eq(v___x_2991_, v___x_3074_);
if (v___x_3075_ == 0)
{
uint8_t v___x_3076_; 
v___x_3076_ = 1;
v___y_3063_ = v___x_3075_;
v___y_3064_ = v___y_3073_;
v___y_3065_ = v___x_3076_;
goto v___jp_3062_;
}
else
{
uint8_t v___x_3077_; 
v___x_3077_ = 0;
v___y_3063_ = v___x_3075_;
v___y_3064_ = v___y_3073_;
v___y_3065_ = v___x_3077_;
goto v___jp_3062_;
}
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2945_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2911_, v___x_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_definition_x3f_2943_);
lean_dec(v_a_2941_);
lean_dec(v_a_2918_);
lean_dec(v_r_2913_);
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
else
{
lean_object* v_a_2954_; size_t v_sz_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v_a_2954_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2945_, 1);
v_sz_2955_ = lean_array_size(v_a_2954_);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2955_, v___x_2956_, v_a_2954_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_definition_x3f_2943_);
lean_dec(v_a_2941_);
lean_dec(v_a_2918_);
lean_dec(v_r_2913_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2966_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_definition_x3f_2943_);
lean_ctor_set(v___x_2967_, 1, v_a_2966_);
v___x_2968_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2941_, v___x_2967_, v_a_2918_);
v_init_2908_ = v___x_2968_;
v_x_2909_ = v_r_2913_;
goto _start;
}
}
}
v___jp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v_a_2971_);
v___x_2973_ = v___x_2920_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
v_definition_x3f_2943_ = v___x_2973_;
goto v___jp_2942_;
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
lean_object* v___x_3085_; 
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_init_2908_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3086_, lean_object* v_k_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = l_Lean_Json_getObjValD(v_j_3086_, v_k_3087_);
v___x_3089_ = l_Lean_Json_getObj_x3f(v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3099_ = lean_box(1);
v___x_3100_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3099_, v_a_3098_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3101_, lean_object* v_k_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3101_, v_k_3102_);
lean_dec_ref(v_k_3102_);
return v_res_3103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = 1;
v___x_3110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3111_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3114_ = lean_string_append(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3117_ = lean_string_append(v___x_3116_, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3120_ = lean_string_append(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = 1;
v___x_3125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3128_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3129_ = lean_string_append(v___x_3128_, v___x_3127_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3132_ = lean_string_append(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = 1;
v___x_3137_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3137_, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3140_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3141_ = lean_string_append(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3144_ = lean_string_append(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3145_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3145_);
v___x_3147_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3145_, v___x_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_json_3145_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3153_ = lean_string_append(v___x_3152_, v_a_3148_);
lean_dec(v_a_3148_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3153_);
v___x_3155_ = v___x_3150_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
else
{
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_json_3145_);
v_a_3158_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3147_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3147_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 0);
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_a_3166_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3145_);
v___x_3168_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3145_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3166_);
lean_dec(v_json_3145_);
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3178_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3178_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3174_ = lean_string_append(v___x_3173_, v_a_3169_);
lean_dec(v_a_3169_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3174_);
v___x_3176_ = v___x_3171_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3166_);
lean_dec(v_json_3145_);
v_a_3179_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3168_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3168_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 0);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_a_3187_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3188_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3189_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3145_, v___x_3188_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_a_3187_);
lean_dec(v_a_3166_);
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3199_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3199_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3194_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3195_ = lean_string_append(v___x_3194_, v_a_3190_);
lean_dec(v_a_3190_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3195_);
v___x_3197_ = v___x_3192_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_a_3187_);
lean_dec(v_a_3166_);
v_a_3200_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3189_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3189_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set_tag(v___x_3202_, 0);
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
v_a_3208_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3210_ = v___x_3189_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3189_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3212_, 0, v_a_3166_);
lean_ctor_set(v___x_3212_, 1, v_a_3187_);
lean_ctor_set(v___x_3212_, 2, v_a_3208_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3217_, lean_object* v_k_3218_, lean_object* v_v_3219_, lean_object* v_t_3220_, lean_object* v_hl_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3218_, v_v_3219_, v_t_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3223_, lean_object* v_k_3224_, lean_object* v_v_3225_, lean_object* v_t_3226_, lean_object* v_hl_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3224_, v_v_3225_, v_t_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3231_, lean_object* v_x_3232_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 0)
{
lean_object* v_k_3233_; lean_object* v_v_3234_; lean_object* v_l_3235_; lean_object* v_r_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_k_3233_ = lean_ctor_get(v_x_3232_, 1);
v_v_3234_ = lean_ctor_get(v_x_3232_, 2);
v_l_3235_ = lean_ctor_get(v_x_3232_, 3);
v_r_3236_ = lean_ctor_get(v_x_3232_, 4);
v___x_3237_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3231_, v_r_3236_);
lean_inc(v_v_3234_);
lean_inc(v_k_3233_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_k_3233_);
lean_ctor_set(v___x_3238_, 1, v_v_3234_);
v___x_3239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
lean_ctor_set(v___x_3239_, 1, v___x_3237_);
v_init_3231_ = v___x_3239_;
v_x_3232_ = v_l_3235_;
goto _start;
}
else
{
return v_init_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3241_, v_x_3242_);
lean_dec(v_x_3242_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3244_, size_t v_i_3245_, lean_object* v_bs_3246_){
_start:
{
uint8_t v___x_3247_; 
v___x_3247_ = lean_usize_dec_lt(v_i_3245_, v_sz_3244_);
if (v___x_3247_ == 0)
{
return v_bs_3246_;
}
else
{
lean_object* v_v_3248_; lean_object* v___x_3249_; lean_object* v_bs_x27_3250_; size_t v___x_3251_; size_t v___x_3252_; lean_object* v___x_3253_; 
v_v_3248_ = lean_array_uget(v_bs_3246_, v_i_3245_);
v___x_3249_ = lean_unsigned_to_nat(0u);
v_bs_x27_3250_ = lean_array_uset(v_bs_3246_, v_i_3245_, v___x_3249_);
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3245_, v___x_3251_);
v___x_3253_ = lean_array_uset(v_bs_x27_3250_, v_i_3245_, v_v_3248_);
v_i_3245_ = v___x_3252_;
v_bs_3246_ = v___x_3253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3255_, lean_object* v_i_3256_, lean_object* v_bs_3257_){
_start:
{
size_t v_sz_boxed_3258_; size_t v_i_boxed_3259_; lean_object* v_res_3260_; 
v_sz_boxed_3258_ = lean_unbox_usize(v_sz_3255_);
lean_dec(v_sz_3255_);
v_i_boxed_3259_ = lean_unbox_usize(v_i_3256_);
lean_dec(v_i_3256_);
v_res_3260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3258_, v_i_boxed_3259_, v_bs_3257_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3261_){
_start:
{
size_t v_sz_3262_; size_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_sz_3262_ = lean_array_size(v_a_3261_);
v___x_3263_ = ((size_t)0ULL);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3262_, v___x_3263_, v_a_3261_);
v___x_3265_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = lean_array_mk(v_a_3266_);
v___x_3268_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3269_){
_start:
{
if (lean_obj_tag(v_x_3269_) == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_box(0);
return v___x_3270_;
}
else
{
lean_object* v_val_3271_; lean_object* v___x_3272_; 
v_val_3271_ = lean_ctor_get(v_x_3269_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v_x_3269_, 1);
v___x_3272_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3271_);
return v___x_3272_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
if (lean_obj_tag(v_a_3273_) == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = l_List_reverse___redArg(v_a_3274_);
return v___x_3275_;
}
else
{
lean_object* v_head_3276_; lean_object* v_tail_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3287_; 
v_head_3276_ = lean_ctor_get(v_a_3273_, 0);
v_tail_3277_ = lean_ctor_get(v_a_3273_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_a_3273_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3279_ = v_a_3273_;
v_isShared_3280_ = v_isSharedCheck_3287_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_tail_3277_);
lean_inc(v_head_3276_);
lean_dec(v_a_3273_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3287_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3281_ = l_Lean_JsonNumber_fromNat(v_head_3276_);
v___x_3282_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 1, v_a_3274_);
lean_ctor_set(v___x_3279_, 0, v___x_3282_);
v___x_3284_ = v___x_3279_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_a_3274_);
v___x_3284_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
v_a_3273_ = v_tail_3277_;
v_a_3274_ = v___x_3284_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3288_, size_t v_i_3289_, lean_object* v_bs_3290_){
_start:
{
uint8_t v___x_3291_; 
v___x_3291_ = lean_usize_dec_lt(v_i_3289_, v_sz_3288_);
if (v___x_3291_ == 0)
{
return v_bs_3290_;
}
else
{
lean_object* v_v_3292_; lean_object* v_startPosLine_3293_; lean_object* v_startPosCharacter_3294_; lean_object* v_endPosLine_3295_; lean_object* v_endPosCharacter_3296_; lean_object* v___x_3297_; lean_object* v_bs_x27_3298_; lean_object* v___y_3300_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_range_3310_; lean_object* v___x_3311_; 
v_v_3292_ = lean_array_uget(v_bs_3290_, v_i_3289_);
v_startPosLine_3293_ = lean_ctor_get(v_v_3292_, 0);
v_startPosCharacter_3294_ = lean_ctor_get(v_v_3292_, 1);
v_endPosLine_3295_ = lean_ctor_get(v_v_3292_, 2);
v_endPosCharacter_3296_ = lean_ctor_get(v_v_3292_, 3);
v___x_3297_ = lean_unsigned_to_nat(0u);
v_bs_x27_3298_ = lean_array_uset(v_bs_3290_, v_i_3289_, v___x_3297_);
v___x_3305_ = lean_box(0);
lean_inc(v_endPosCharacter_3296_);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_endPosCharacter_3296_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
lean_inc(v_endPosLine_3295_);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_endPosLine_3295_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
lean_inc(v_startPosCharacter_3294_);
v___x_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3308_, 0, v_startPosCharacter_3294_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_inc(v_startPosLine_3293_);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_startPosLine_3293_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v_range_3310_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3309_, v___x_3305_);
v___x_3311_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3292_);
lean_dec(v_v_3292_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v___x_3312_; 
v___x_3312_ = l_List_appendTR___redArg(v_range_3310_, v___x_3305_);
v___y_3300_ = v___x_3312_;
goto v___jp_3299_;
}
else
{
lean_object* v_val_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3322_; 
v_val_3313_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3315_ = v___x_3311_;
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_val_3313_);
lean_dec(v___x_3311_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3322_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 3);
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_val_3313_);
v___x_3318_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v___x_3305_);
v___x_3320_ = l_List_appendTR___redArg(v_range_3310_, v___x_3319_);
v___y_3300_ = v___x_3320_;
goto v___jp_3299_;
}
}
}
v___jp_3299_:
{
size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3289_, v___x_3301_);
v___x_3303_ = lean_array_uset(v_bs_x27_3298_, v_i_3289_, v___y_3300_);
v_i_3289_ = v___x_3302_;
v_bs_3290_ = v___x_3303_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3323_, lean_object* v_i_3324_, lean_object* v_bs_3325_){
_start:
{
size_t v_sz_boxed_3326_; size_t v_i_boxed_3327_; lean_object* v_res_3328_; 
v_sz_boxed_3326_ = lean_unbox_usize(v_sz_3323_);
lean_dec(v_sz_3323_);
v_i_boxed_3327_ = lean_unbox_usize(v_i_3324_);
lean_dec(v_i_3324_);
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3326_, v_i_boxed_3327_, v_bs_3325_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3329_, size_t v_i_3330_, lean_object* v_bs_3331_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_usize_dec_lt(v_i_3330_, v_sz_3329_);
if (v___x_3332_ == 0)
{
return v_bs_3331_;
}
else
{
lean_object* v_v_3333_; lean_object* v___x_3334_; lean_object* v_bs_x27_3335_; lean_object* v___x_3336_; size_t v___x_3337_; size_t v___x_3338_; lean_object* v___x_3339_; 
v_v_3333_ = lean_array_uget(v_bs_3331_, v_i_3330_);
v___x_3334_ = lean_unsigned_to_nat(0u);
v_bs_x27_3335_ = lean_array_uset(v_bs_3331_, v_i_3330_, v___x_3334_);
v___x_3336_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3333_);
v___x_3337_ = ((size_t)1ULL);
v___x_3338_ = lean_usize_add(v_i_3330_, v___x_3337_);
v___x_3339_ = lean_array_uset(v_bs_x27_3335_, v_i_3330_, v___x_3336_);
v_i_3330_ = v___x_3338_;
v_bs_3331_ = v___x_3339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3341_, lean_object* v_i_3342_, lean_object* v_bs_3343_){
_start:
{
size_t v_sz_boxed_3344_; size_t v_i_boxed_3345_; lean_object* v_res_3346_; 
v_sz_boxed_3344_ = lean_unbox_usize(v_sz_3341_);
lean_dec(v_sz_3341_);
v_i_boxed_3345_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_res_3346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3344_, v_i_boxed_3345_, v_bs_3343_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3347_){
_start:
{
size_t v_sz_3348_; size_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_sz_3348_ = lean_array_size(v_a_3347_);
v___x_3349_ = ((size_t)0ULL);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3348_, v___x_3349_, v_a_3347_);
v___x_3351_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
if (lean_obj_tag(v_a_3352_) == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = l_List_reverse___redArg(v_a_3353_);
return v___x_3354_;
}
else
{
lean_object* v_head_3355_; lean_object* v_snd_3356_; lean_object* v_tail_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3426_; 
v_head_3355_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_head_3355_);
v_snd_3356_ = lean_ctor_get(v_head_3355_, 1);
lean_inc(v_snd_3356_);
v_tail_3357_ = lean_ctor_get(v_a_3352_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_a_3352_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v_a_3352_, 0);
lean_dec(v_unused_3427_);
v___x_3359_ = v_a_3352_;
v_isShared_3360_ = v_isSharedCheck_3426_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_tail_3357_);
lean_dec(v_a_3352_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3426_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_fst_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3424_; 
v_fst_3361_ = lean_ctor_get(v_head_3355_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_head_3355_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v_head_3355_, 1);
lean_dec(v_unused_3425_);
v___x_3363_ = v_head_3355_;
v_isShared_3364_ = v_isSharedCheck_3424_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_fst_3361_);
lean_dec(v_head_3355_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3424_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v_definition_x3f_3365_; lean_object* v_usages_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3423_; 
v_definition_x3f_3365_ = lean_ctor_get(v_snd_3356_, 0);
v_usages_3366_ = lean_ctor_get(v_snd_3356_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_snd_3356_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3368_ = v_snd_3356_;
v_isShared_3369_ = v_isSharedCheck_3423_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_usages_3366_);
lean_inc(v_definition_x3f_3365_);
lean_dec(v_snd_3356_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3423_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___y_3374_; lean_object* v___y_3397_; 
v___x_3370_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3361_);
v___x_3371_ = l_Lean_Json_compress(v___x_3370_);
v___x_3372_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3365_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_box(0);
v___y_3374_ = v___x_3399_;
goto v___jp_3373_;
}
else
{
lean_object* v_val_3400_; lean_object* v_startPosLine_3401_; lean_object* v_startPosCharacter_3402_; lean_object* v_endPosLine_3403_; lean_object* v_endPosCharacter_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v_range_3410_; lean_object* v___x_3411_; 
v_val_3400_ = lean_ctor_get(v_definition_x3f_3365_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v_definition_x3f_3365_, 1);
v_startPosLine_3401_ = lean_ctor_get(v_val_3400_, 0);
v_startPosCharacter_3402_ = lean_ctor_get(v_val_3400_, 1);
v_endPosLine_3403_ = lean_ctor_get(v_val_3400_, 2);
v_endPosCharacter_3404_ = lean_ctor_get(v_val_3400_, 3);
v___x_3405_ = lean_box(0);
lean_inc(v_endPosCharacter_3404_);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_endPosCharacter_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
lean_inc(v_endPosLine_3403_);
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v_endPosLine_3403_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
lean_inc(v_startPosCharacter_3402_);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v_startPosCharacter_3402_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
lean_inc(v_startPosLine_3401_);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_startPosLine_3401_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v_range_3410_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3409_, v___x_3405_);
v___x_3411_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3400_);
lean_dec(v_val_3400_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = l_List_appendTR___redArg(v_range_3410_, v___x_3405_);
v___y_3397_ = v___x_3412_;
goto v___jp_3396_;
}
else
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3422_; 
v_val_3413_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3415_ = v___x_3411_;
v_isShared_3416_ = v_isSharedCheck_3422_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v___x_3411_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3422_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set_tag(v___x_3415_, 3);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_val_3413_);
v___x_3418_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___x_3405_);
v___x_3420_ = l_List_appendTR___redArg(v_range_3410_, v___x_3419_);
v___y_3397_ = v___x_3420_;
goto v___jp_3396_;
}
}
}
}
v___jp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3374_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 1, v___x_3375_);
lean_ctor_set(v___x_3363_, 0, v___x_3372_);
v___x_3377_ = v___x_3363_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; size_t v_sz_3379_; size_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3378_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3379_ = lean_array_size(v_usages_3366_);
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3379_, v___x_3380_, v_usages_3366_);
v___x_3382_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3381_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3382_);
lean_ctor_set(v___x_3368_, 0, v___x_3378_);
v___x_3384_ = v___x_3368_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3385_ = lean_box(0);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3385_);
lean_ctor_set(v___x_3359_, 0, v___x_3384_);
v___x_3387_ = v___x_3359_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3377_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = l_Lean_Json_mkObj(v___x_3388_);
lean_dec_ref_known(v___x_3388_, 2);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3371_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v_a_3353_);
v_a_3352_ = v_tail_3357_;
v_a_3353_ = v___x_3391_;
goto _start;
}
}
}
}
v___jp_3396_:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3397_);
v___y_3374_ = v___x_3398_;
goto v___jp_3373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
if (lean_obj_tag(v_a_3428_) == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = l_List_reverse___redArg(v_a_3429_);
return v___x_3430_;
}
else
{
lean_object* v_head_3431_; lean_object* v_snd_3432_; lean_object* v_tail_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3485_; 
v_head_3431_ = lean_ctor_get(v_a_3428_, 0);
lean_inc(v_head_3431_);
v_snd_3432_ = lean_ctor_get(v_head_3431_, 1);
lean_inc(v_snd_3432_);
v_tail_3433_ = lean_ctor_get(v_a_3428_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_a_3428_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; 
v_unused_3486_ = lean_ctor_get(v_a_3428_, 0);
lean_dec(v_unused_3486_);
v___x_3435_ = v_a_3428_;
v_isShared_3436_ = v_isSharedCheck_3485_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_tail_3433_);
lean_dec(v_a_3428_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3485_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_fst_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3483_; 
v_fst_3437_ = lean_ctor_get(v_head_3431_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_head_3431_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_head_3431_, 1);
lean_dec(v_unused_3484_);
v___x_3439_ = v_head_3431_;
v_isShared_3440_ = v_isSharedCheck_3483_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_fst_3437_);
lean_dec(v_head_3431_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3483_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_rangeStartPosLine_3441_; lean_object* v_rangeStartPosCharacter_3442_; lean_object* v_rangeEndPosLine_3443_; lean_object* v_rangeEndPosCharacter_3444_; lean_object* v_selectionRangeStartPosLine_3445_; lean_object* v_selectionRangeStartPosCharacter_3446_; lean_object* v_selectionRangeEndPosLine_3447_; lean_object* v_selectionRangeEndPosCharacter_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v_rangeStartPosLine_3441_ = lean_ctor_get(v_snd_3432_, 0);
lean_inc(v_rangeStartPosLine_3441_);
v_rangeStartPosCharacter_3442_ = lean_ctor_get(v_snd_3432_, 1);
lean_inc(v_rangeStartPosCharacter_3442_);
v_rangeEndPosLine_3443_ = lean_ctor_get(v_snd_3432_, 2);
lean_inc(v_rangeEndPosLine_3443_);
v_rangeEndPosCharacter_3444_ = lean_ctor_get(v_snd_3432_, 3);
lean_inc(v_rangeEndPosCharacter_3444_);
v_selectionRangeStartPosLine_3445_ = lean_ctor_get(v_snd_3432_, 4);
lean_inc(v_selectionRangeStartPosLine_3445_);
v_selectionRangeStartPosCharacter_3446_ = lean_ctor_get(v_snd_3432_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3446_);
v_selectionRangeEndPosLine_3447_ = lean_ctor_get(v_snd_3432_, 6);
lean_inc(v_selectionRangeEndPosLine_3447_);
v_selectionRangeEndPosCharacter_3448_ = lean_ctor_get(v_snd_3432_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3448_);
lean_dec(v_snd_3432_);
v___x_3449_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3441_);
v___x_3450_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
v___x_3451_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3442_);
v___x_3452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
v___x_3453_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3443_);
v___x_3454_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
v___x_3455_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3444_);
v___x_3456_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
v___x_3457_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3445_);
v___x_3458_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
v___x_3459_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3446_);
v___x_3460_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
v___x_3461_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3447_);
v___x_3462_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
v___x_3463_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3448_);
v___x_3464_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
v___x_3465_ = lean_unsigned_to_nat(8u);
v___x_3466_ = lean_mk_empty_array_with_capacity(v___x_3465_);
v___x_3467_ = lean_array_push(v___x_3466_, v___x_3450_);
v___x_3468_ = lean_array_push(v___x_3467_, v___x_3452_);
v___x_3469_ = lean_array_push(v___x_3468_, v___x_3454_);
v___x_3470_ = lean_array_push(v___x_3469_, v___x_3456_);
v___x_3471_ = lean_array_push(v___x_3470_, v___x_3458_);
v___x_3472_ = lean_array_push(v___x_3471_, v___x_3460_);
v___x_3473_ = lean_array_push(v___x_3472_, v___x_3462_);
v___x_3474_ = lean_array_push(v___x_3473_, v___x_3464_);
v___x_3475_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3475_);
v___x_3477_ = v___x_3439_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_fst_3437_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 1, v_a_3429_);
lean_ctor_set(v___x_3435_, 0, v___x_3477_);
v___x_3479_ = v___x_3435_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3429_);
v___x_3479_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
v_a_3428_ = v_tail_3433_;
v_a_3429_ = v___x_3479_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3487_, lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
lean_object* v_k_3489_; lean_object* v_v_3490_; lean_object* v_l_3491_; lean_object* v_r_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_k_3489_ = lean_ctor_get(v_x_3488_, 1);
v_v_3490_ = lean_ctor_get(v_x_3488_, 2);
v_l_3491_ = lean_ctor_get(v_x_3488_, 3);
v_r_3492_ = lean_ctor_get(v_x_3488_, 4);
v___x_3493_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3487_, v_r_3492_);
lean_inc(v_v_3490_);
lean_inc(v_k_3489_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v_k_3489_);
lean_ctor_set(v___x_3494_, 1, v_v_3490_);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3494_);
lean_ctor_set(v___x_3495_, 1, v___x_3493_);
v_init_3487_ = v___x_3495_;
v_x_3488_ = v_l_3491_;
goto _start;
}
else
{
return v_init_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3497_, lean_object* v_x_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3497_, v_x_3498_);
lean_dec(v_x_3498_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3500_){
_start:
{
lean_object* v_version_3501_; lean_object* v_references_3502_; lean_object* v_decls_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_version_3501_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_version_3501_);
v_references_3502_ = lean_ctor_get(v_x_3500_, 1);
lean_inc(v_references_3502_);
v_decls_3503_ = lean_ctor_get(v_x_3500_, 2);
lean_inc(v_decls_3503_);
lean_dec_ref(v_x_3500_);
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3505_ = l_Lean_JsonNumber_fromNat(v_version_3501_);
v___x_3506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3504_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3511_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3508_, v_references_3502_);
lean_dec(v_references_3502_);
v___x_3512_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3511_, v___x_3508_);
v___x_3513_ = l_Lean_Json_mkObj(v___x_3512_);
lean_dec(v___x_3512_);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3510_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
lean_ctor_set(v___x_3515_, 1, v___x_3508_);
v___x_3516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3517_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3508_, v_decls_3503_);
lean_dec(v_decls_3503_);
v___x_3518_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3517_, v___x_3508_);
v___x_3519_ = l_Lean_Json_mkObj(v___x_3518_);
lean_dec(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3516_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3508_);
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v___x_3508_);
v___x_3523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3515_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3509_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3526_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3524_, v___x_3525_);
v___x_3527_ = l_Lean_Json_mkObj(v___x_3526_);
lean_dec(v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3530_, size_t v_i_3531_, lean_object* v_bs_3532_){
_start:
{
uint8_t v___x_3533_; 
v___x_3533_ = lean_usize_dec_lt(v_i_3531_, v_sz_3530_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_bs_3532_);
return v___x_3534_;
}
else
{
lean_object* v_v_3535_; lean_object* v___x_3536_; 
v_v_3535_ = lean_array_uget_borrowed(v_bs_3532_, v_i_3531_);
lean_inc(v_v_3535_);
v___x_3536_ = l_Lean_Json_getStr_x3f(v_v_3535_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_bs_3532_);
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3546_; lean_object* v_bs_x27_3547_; size_t v___x_3548_; size_t v___x_3549_; lean_object* v___x_3550_; 
v_a_3545_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3546_ = lean_unsigned_to_nat(0u);
v_bs_x27_3547_ = lean_array_uset(v_bs_3532_, v_i_3531_, v___x_3546_);
v___x_3548_ = ((size_t)1ULL);
v___x_3549_ = lean_usize_add(v_i_3531_, v___x_3548_);
v___x_3550_ = lean_array_uset(v_bs_x27_3547_, v_i_3531_, v_a_3545_);
v_i_3531_ = v___x_3549_;
v_bs_3532_ = v___x_3550_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3552_, lean_object* v_i_3553_, lean_object* v_bs_3554_){
_start:
{
size_t v_sz_boxed_3555_; size_t v_i_boxed_3556_; lean_object* v_res_3557_; 
v_sz_boxed_3555_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v_i_boxed_3556_ = lean_unbox_usize(v_i_3553_);
lean_dec(v_i_3553_);
v_res_3557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3555_, v_i_boxed_3556_, v_bs_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 4)
{
lean_object* v_elems_3559_; size_t v_sz_3560_; size_t v___x_3561_; lean_object* v___x_3562_; 
v_elems_3559_ = lean_ctor_get(v_x_3558_, 0);
lean_inc_ref(v_elems_3559_);
lean_dec_ref_known(v_x_3558_, 1);
v_sz_3560_ = lean_array_size(v_elems_3559_);
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3560_, v___x_3561_, v_elems_3559_);
return v___x_3562_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3563_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3564_ = lean_unsigned_to_nat(80u);
v___x_3565_ = l_Lean_Json_pretty(v_x_3558_, v___x_3564_);
v___x_3566_ = lean_string_append(v___x_3563_, v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3568_ = lean_string_append(v___x_3566_, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3570_, lean_object* v_k_3571_){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = l_Lean_Json_getObjValD(v_j_3570_, v_k_3571_);
v___x_3573_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3574_, lean_object* v_k_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3574_, v_k_3575_);
lean_dec_ref(v_k_3575_);
return v_res_3576_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = 1;
v___x_3584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3585_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3584_, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3587_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3588_ = lean_string_append(v___x_3587_, v___x_3586_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = 1;
v___x_3592_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3592_, v___x_3591_);
return v___x_3593_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3595_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3596_ = lean_string_append(v___x_3595_, v___x_3594_);
return v___x_3596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3598_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3599_ = lean_string_append(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3602_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3600_, v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3608_ = lean_string_append(v___x_3607_, v_a_3603_);
lean_dec(v_a_3603_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3608_);
v___x_3610_ = v___x_3605_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
else
{
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_a_3613_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3602_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3602_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 0);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3602_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3602_);
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
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3631_, size_t v_i_3632_, lean_object* v_bs_3633_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_lt(v_i_3632_, v_sz_3631_);
if (v___x_3634_ == 0)
{
return v_bs_3633_;
}
else
{
lean_object* v_v_3635_; lean_object* v___x_3636_; lean_object* v_bs_x27_3637_; lean_object* v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; lean_object* v___x_3641_; 
v_v_3635_ = lean_array_uget(v_bs_3633_, v_i_3632_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v_bs_x27_3637_ = lean_array_uset(v_bs_3633_, v_i_3632_, v___x_3636_);
v___x_3638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_v_3635_);
v___x_3639_ = ((size_t)1ULL);
v___x_3640_ = lean_usize_add(v_i_3632_, v___x_3639_);
v___x_3641_ = lean_array_uset(v_bs_x27_3637_, v_i_3632_, v___x_3638_);
v_i_3632_ = v___x_3640_;
v_bs_3633_ = v___x_3641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3643_, lean_object* v_i_3644_, lean_object* v_bs_3645_){
_start:
{
size_t v_sz_boxed_3646_; size_t v_i_boxed_3647_; lean_object* v_res_3648_; 
v_sz_boxed_3646_ = lean_unbox_usize(v_sz_3643_);
lean_dec(v_sz_3643_);
v_i_boxed_3647_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_res_3648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3646_, v_i_boxed_3647_, v_bs_3645_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3649_){
_start:
{
size_t v_sz_3650_; size_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v_sz_3650_ = lean_array_size(v_a_3649_);
v___x_3651_ = ((size_t)0ULL);
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3650_, v___x_3651_, v_a_3649_);
v___x_3653_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3654_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3655_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3656_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3654_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___x_3658_);
v___x_3661_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3662_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3660_, v___x_3661_);
v___x_3663_ = l_Lean_Json_mkObj(v___x_3662_);
lean_dec(v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3666_, lean_object* v_k_3667_){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = l_Lean_Json_getObjValD(v_j_3666_, v_k_3667_);
v___x_3669_ = l_Lean_Json_getStr_x3f(v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3670_, lean_object* v_k_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3670_, v_k_3671_);
lean_dec_ref(v_k_3671_);
return v_res_3672_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = 1;
v___x_3680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3680_, v___x_3679_);
return v___x_3681_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3684_ = lean_string_append(v___x_3683_, v___x_3682_);
return v___x_3684_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = 1;
v___x_3688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3688_, v___x_3687_);
return v___x_3689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3692_ = lean_string_append(v___x_3691_, v___x_3690_);
return v___x_3692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3695_ = lean_string_append(v___x_3694_, v___x_3693_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3696_, v___x_3697_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3708_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3704_ = lean_string_append(v___x_3703_, v_a_3699_);
lean_dec(v_a_3699_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3704_);
v___x_3706_ = v___x_3701_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
v_a_3709_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3698_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3698_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 0);
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_a_3717_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3698_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3698_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3727_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_x_3727_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_box(0);
v___x_3732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___x_3731_);
v___x_3734_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3735_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3733_, v___x_3734_);
v___x_3736_ = l_Lean_Json_mkObj(v___x_3735_);
lean_dec(v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3739_){
_start:
{
if (lean_obj_tag(v_x_3739_) == 0)
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_unsigned_to_nat(0u);
return v___x_3740_;
}
else
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_unsigned_to_nat(1u);
return v___x_3741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3742_);
lean_dec_ref(v_x_3742_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3744_, lean_object* v_k_3745_){
_start:
{
if (lean_obj_tag(v_t_3744_) == 0)
{
lean_object* v_namespace_3746_; lean_object* v_exceptions_3747_; lean_object* v___x_3748_; 
v_namespace_3746_ = lean_ctor_get(v_t_3744_, 0);
lean_inc(v_namespace_3746_);
v_exceptions_3747_ = lean_ctor_get(v_t_3744_, 1);
lean_inc_ref(v_exceptions_3747_);
lean_dec_ref_known(v_t_3744_, 2);
v___x_3748_ = lean_apply_2(v_k_3745_, v_namespace_3746_, v_exceptions_3747_);
return v___x_3748_;
}
else
{
lean_object* v_from_3749_; lean_object* v_to_3750_; lean_object* v___x_3751_; 
v_from_3749_ = lean_ctor_get(v_t_3744_, 0);
lean_inc(v_from_3749_);
v_to_3750_ = lean_ctor_get(v_t_3744_, 1);
lean_inc(v_to_3750_);
lean_dec_ref_known(v_t_3744_, 2);
v___x_3751_ = lean_apply_2(v_k_3745_, v_from_3749_, v_to_3750_);
return v___x_3751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3752_, lean_object* v_ctorIdx_3753_, lean_object* v_t_3754_, lean_object* v_h_3755_, lean_object* v_k_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3754_, v_k_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3758_, lean_object* v_ctorIdx_3759_, lean_object* v_t_3760_, lean_object* v_h_3761_, lean_object* v_k_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3758_, v_ctorIdx_3759_, v_t_3760_, v_h_3761_, v_k_3762_);
lean_dec(v_ctorIdx_3759_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3764_, lean_object* v_allExcept_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3764_, v_allExcept_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3767_, lean_object* v_t_3768_, lean_object* v_h_3769_, lean_object* v_allExcept_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3768_, v_allExcept_3770_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3772_, lean_object* v_renamed_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3772_, v_renamed_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3775_, lean_object* v_t_3776_, lean_object* v_h_3777_, lean_object* v_renamed_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3776_, v_renamed_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_bs_3782_){
_start:
{
uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_bs_3782_);
return v___x_3784_;
}
else
{
lean_object* v_v_3785_; lean_object* v___x_3786_; 
v_v_3785_ = lean_array_uget_borrowed(v_bs_3782_, v_i_3781_);
lean_inc(v_v_3785_);
v___x_3786_ = l_Lean_Name_fromJson_x3f(v_v_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_bs_3782_);
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v_bs_x27_3797_; size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v_a_3795_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3786_, 1);
v___x_3796_ = lean_unsigned_to_nat(0u);
v_bs_x27_3797_ = lean_array_uset(v_bs_3782_, v_i_3781_, v___x_3796_);
v___x_3798_ = ((size_t)1ULL);
v___x_3799_ = lean_usize_add(v_i_3781_, v___x_3798_);
v___x_3800_ = lean_array_uset(v_bs_x27_3797_, v_i_3781_, v_a_3795_);
v_i_3781_ = v___x_3799_;
v_bs_3782_ = v___x_3800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3802_, lean_object* v_i_3803_, lean_object* v_bs_3804_){
_start:
{
size_t v_sz_boxed_3805_; size_t v_i_boxed_3806_; lean_object* v_res_3807_; 
v_sz_boxed_3805_ = lean_unbox_usize(v_sz_3802_);
lean_dec(v_sz_3802_);
v_i_boxed_3806_ = lean_unbox_usize(v_i_3803_);
lean_dec(v_i_3803_);
v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3805_, v_i_boxed_3806_, v_bs_3804_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3808_){
_start:
{
if (lean_obj_tag(v_x_3808_) == 4)
{
lean_object* v_elems_3809_; size_t v_sz_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v_elems_3809_ = lean_ctor_get(v_x_3808_, 0);
lean_inc_ref(v_elems_3809_);
lean_dec_ref_known(v_x_3808_, 1);
v_sz_3810_ = lean_array_size(v_elems_3809_);
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3810_, v___x_3811_, v_elems_3809_);
return v___x_3812_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3813_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3814_ = lean_unsigned_to_nat(80u);
v___x_3815_ = l_Lean_Json_pretty(v_x_3808_, v___x_3814_);
v___x_3816_ = lean_string_append(v___x_3813_, v___x_3815_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3818_ = lean_string_append(v___x_3816_, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
return v___x_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3854_){
_start:
{
lean_object* v___x_3855_; 
lean_inc(v_json_3854_);
v___x_3855_ = l_Lean_Json_getTag_x3f(v_json_3854_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; 
lean_dec(v_json_3854_);
v___x_3856_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3856_;
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v_val_3857_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3858_ = lean_box(0);
v___x_3859_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3860_ = lean_string_dec_eq(v_val_3857_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3862_ = lean_string_dec_eq(v_val_3857_, v___x_3861_);
lean_dec(v_val_3857_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec(v_json_3854_);
v___x_3863_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3863_;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = lean_unsigned_to_nat(2u);
v___x_3865_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3866_ = l_Lean_Json_parseCtorFields(v_json_3854_, v___x_3861_, v___x_3864_, v___x_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3875_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3866_, 1);
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = lean_array_get_borrowed(v___x_3858_, v_a_3875_, v___x_3876_);
lean_inc(v___x_3877_);
v___x_3878_ = l_Lean_Name_fromJson_x3f(v___x_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_a_3875_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_a_3887_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3888_ = lean_unsigned_to_nat(1u);
v___x_3889_ = lean_array_get(v___x_3858_, v_a_3875_, v___x_3888_);
lean_dec(v_a_3875_);
v___x_3890_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3889_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_a_3887_);
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3907_; 
v_a_3899_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3901_ = v___x_3890_;
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3890_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3887_);
lean_ctor_set(v___x_3903_, 1, v_a_3899_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v_val_3857_);
v___x_3908_ = lean_unsigned_to_nat(2u);
v___x_3909_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3910_ = l_Lean_Json_parseCtorFields(v_json_3854_, v___x_3859_, v___x_3908_, v___x_3909_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3919_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3920_ = lean_unsigned_to_nat(0u);
v___x_3921_ = lean_array_get_borrowed(v___x_3858_, v_a_3919_, v___x_3920_);
lean_inc(v___x_3921_);
v___x_3922_ = l_Lean_Name_fromJson_x3f(v___x_3921_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_a_3919_);
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_a_3931_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3932_ = lean_unsigned_to_nat(1u);
v___x_3933_ = lean_array_get(v___x_3858_, v_a_3919_, v___x_3932_);
lean_dec(v_a_3919_);
v___x_3934_ = l_Lean_Name_fromJson_x3f(v___x_3933_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v_a_3931_);
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3951_; 
v_a_3943_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3945_ = v___x_3934_;
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3934_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3951_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_a_3931_);
lean_ctor_set(v___x_3947_, 1, v_a_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3954_, size_t v_i_3955_, lean_object* v_bs_3956_){
_start:
{
uint8_t v___x_3957_; 
v___x_3957_ = lean_usize_dec_lt(v_i_3955_, v_sz_3954_);
if (v___x_3957_ == 0)
{
return v_bs_3956_;
}
else
{
lean_object* v_v_3958_; lean_object* v___x_3959_; lean_object* v_bs_x27_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; size_t v___x_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v_v_3958_ = lean_array_uget(v_bs_3956_, v_i_3955_);
v___x_3959_ = lean_unsigned_to_nat(0u);
v_bs_x27_3960_ = lean_array_uset(v_bs_3956_, v_i_3955_, v___x_3959_);
v___x_3961_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3958_, v___x_3957_);
v___x_3962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = ((size_t)1ULL);
v___x_3964_ = lean_usize_add(v_i_3955_, v___x_3963_);
v___x_3965_ = lean_array_uset(v_bs_x27_3960_, v_i_3955_, v___x_3962_);
v_i_3955_ = v___x_3964_;
v_bs_3956_ = v___x_3965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3967_, lean_object* v_i_3968_, lean_object* v_bs_3969_){
_start:
{
size_t v_sz_boxed_3970_; size_t v_i_boxed_3971_; lean_object* v_res_3972_; 
v_sz_boxed_3970_ = lean_unbox_usize(v_sz_3967_);
lean_dec(v_sz_3967_);
v_i_boxed_3971_ = lean_unbox_usize(v_i_3968_);
lean_dec(v_i_3968_);
v_res_3972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3970_, v_i_boxed_3971_, v_bs_3969_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3973_){
_start:
{
size_t v_sz_3974_; size_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_sz_3974_ = lean_array_size(v_a_3973_);
v___x_3975_ = ((size_t)0ULL);
v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3974_, v___x_3975_, v_a_3973_);
v___x_3977_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3978_){
_start:
{
if (lean_obj_tag(v_x_3978_) == 0)
{
lean_object* v_namespace_3979_; lean_object* v_exceptions_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4002_; 
v_namespace_3979_ = lean_ctor_get(v_x_3978_, 0);
v_exceptions_3980_ = lean_ctor_get(v_x_3978_, 1);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_x_3978_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3982_ = v_x_3978_;
v_isShared_3983_ = v_isSharedCheck_4002_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_exceptions_3980_);
lean_inc(v_namespace_3979_);
lean_dec(v_x_3978_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4002_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3984_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3986_ = 1;
v___x_3987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3979_, v___x_3986_);
v___x_3988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_3988_);
lean_ctor_set(v___x_3982_, 0, v___x_3985_);
v___x_3990_ = v___x_3982_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3992_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3980_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = lean_box(0);
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3990_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l_Lean_Json_mkObj(v___x_3996_);
lean_dec_ref_known(v___x_3996_, 2);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3984_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
lean_ctor_set(v___x_3999_, 1, v___x_3994_);
v___x_4000_ = l_Lean_Json_mkObj(v___x_3999_);
lean_dec_ref_known(v___x_3999_, 2);
return v___x_4000_;
}
}
}
else
{
lean_object* v_from_4003_; lean_object* v_to_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4027_; 
v_from_4003_ = lean_ctor_get(v_x_3978_, 0);
v_to_4004_ = lean_ctor_get(v_x_3978_, 1);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_x_3978_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4006_ = v_x_3978_;
v_isShared_4007_ = v_isSharedCheck_4027_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_to_4004_);
lean_inc(v_from_4003_);
lean_dec(v_x_3978_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4027_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4008_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_4009_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_4010_ = 1;
v___x_4011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_4003_, v___x_4010_);
v___x_4012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 0);
lean_ctor_set(v___x_4006_, 1, v___x_4012_);
lean_ctor_set(v___x_4006_, 0, v___x_4009_);
v___x_4014_ = v___x_4006_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4009_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4015_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_4016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_4004_, v___x_4010_);
v___x_4017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4015_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = lean_box(0);
v___x_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4018_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4014_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_Json_mkObj(v___x_4021_);
lean_dec_ref_known(v___x_4021_, 2);
v___x_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4008_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
v___x_4024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v___x_4019_);
v___x_4025_ = l_Lean_Json_mkObj(v___x_4024_);
lean_dec_ref_known(v___x_4024_, 2);
return v___x_4025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4030_, size_t v_i_4031_, lean_object* v_bs_4032_){
_start:
{
uint8_t v___x_4033_; 
v___x_4033_ = lean_usize_dec_lt(v_i_4031_, v_sz_4030_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_bs_4032_);
return v___x_4034_;
}
else
{
lean_object* v_v_4035_; lean_object* v___x_4036_; 
v_v_4035_ = lean_array_uget_borrowed(v_bs_4032_, v_i_4031_);
lean_inc(v_v_4035_);
v___x_4036_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_4035_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v_bs_4032_);
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4046_; lean_object* v_bs_x27_4047_; size_t v___x_4048_; size_t v___x_4049_; lean_object* v___x_4050_; 
v_a_4045_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4046_ = lean_unsigned_to_nat(0u);
v_bs_x27_4047_ = lean_array_uset(v_bs_4032_, v_i_4031_, v___x_4046_);
v___x_4048_ = ((size_t)1ULL);
v___x_4049_ = lean_usize_add(v_i_4031_, v___x_4048_);
v___x_4050_ = lean_array_uset(v_bs_x27_4047_, v_i_4031_, v_a_4045_);
v_i_4031_ = v___x_4049_;
v_bs_4032_ = v___x_4050_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4052_, lean_object* v_i_4053_, lean_object* v_bs_4054_){
_start:
{
size_t v_sz_boxed_4055_; size_t v_i_boxed_4056_; lean_object* v_res_4057_; 
v_sz_boxed_4055_ = lean_unbox_usize(v_sz_4052_);
lean_dec(v_sz_4052_);
v_i_boxed_4056_ = lean_unbox_usize(v_i_4053_);
lean_dec(v_i_4053_);
v_res_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4055_, v_i_boxed_4056_, v_bs_4054_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4058_){
_start:
{
if (lean_obj_tag(v_x_4058_) == 4)
{
lean_object* v_elems_4059_; size_t v_sz_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v_elems_4059_ = lean_ctor_get(v_x_4058_, 0);
lean_inc_ref(v_elems_4059_);
lean_dec_ref_known(v_x_4058_, 1);
v_sz_4060_ = lean_array_size(v_elems_4059_);
v___x_4061_ = ((size_t)0ULL);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4060_, v___x_4061_, v_elems_4059_);
return v___x_4062_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4063_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4064_ = lean_unsigned_to_nat(80u);
v___x_4065_ = l_Lean_Json_pretty(v_x_4058_, v___x_4064_);
v___x_4066_ = lean_string_append(v___x_4063_, v___x_4065_);
lean_dec_ref(v___x_4065_);
v___x_4067_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4068_ = lean_string_append(v___x_4066_, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4070_, lean_object* v_k_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = l_Lean_Json_getObjValD(v_j_4070_, v_k_4071_);
v___x_4073_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4072_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4074_, lean_object* v_k_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4074_, v_k_4075_);
lean_dec_ref(v_k_4075_);
return v_res_4076_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4083_ = 1;
v___x_4084_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4084_, v___x_4083_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4086_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4087_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4088_ = lean_string_append(v___x_4087_, v___x_4086_);
return v___x_4088_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = 1;
v___x_4092_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4092_, v___x_4091_);
return v___x_4093_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4095_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4096_ = lean_string_append(v___x_4095_, v___x_4094_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4099_ = lean_string_append(v___x_4098_, v___x_4097_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = 1;
v___x_4104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4104_, v___x_4103_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4108_ = lean_string_append(v___x_4107_, v___x_4106_);
return v___x_4108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4111_ = lean_string_append(v___x_4110_, v___x_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4112_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4112_);
v___x_4114_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4112_, v___x_4113_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_json_4112_);
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4117_ = v___x_4114_;
v_isShared_4118_ = v_isSharedCheck_4124_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4124_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4120_ = lean_string_append(v___x_4119_, v_a_4115_);
lean_dec(v_a_4115_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v___x_4120_);
v___x_4122_ = v___x_4117_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v_json_4112_);
v_a_4125_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4114_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4114_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 0);
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_a_4133_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4114_, 1);
v___x_4134_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4112_, v___x_4134_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v_a_4133_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4140_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4141_ = lean_string_append(v___x_4140_, v_a_4136_);
lean_dec(v_a_4136_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4141_);
v___x_4143_ = v___x_4138_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
else
{
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v_a_4133_);
v_a_4146_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4135_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4135_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set_tag(v___x_4148_, 0);
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4162_; 
v_a_4154_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4156_ = v___x_4135_;
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4135_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v_a_4133_);
lean_ctor_set(v___x_4158_, 1, v_a_4154_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4158_);
v___x_4160_ = v___x_4156_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4165_, size_t v_i_4166_, lean_object* v_bs_4167_){
_start:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_usize_dec_lt(v_i_4166_, v_sz_4165_);
if (v___x_4168_ == 0)
{
return v_bs_4167_;
}
else
{
lean_object* v_v_4169_; lean_object* v___x_4170_; lean_object* v_bs_x27_4171_; lean_object* v___x_4172_; size_t v___x_4173_; size_t v___x_4174_; lean_object* v___x_4175_; 
v_v_4169_ = lean_array_uget(v_bs_4167_, v_i_4166_);
v___x_4170_ = lean_unsigned_to_nat(0u);
v_bs_x27_4171_ = lean_array_uset(v_bs_4167_, v_i_4166_, v___x_4170_);
v___x_4172_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4169_);
v___x_4173_ = ((size_t)1ULL);
v___x_4174_ = lean_usize_add(v_i_4166_, v___x_4173_);
v___x_4175_ = lean_array_uset(v_bs_x27_4171_, v_i_4166_, v___x_4172_);
v_i_4166_ = v___x_4174_;
v_bs_4167_ = v___x_4175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4177_, lean_object* v_i_4178_, lean_object* v_bs_4179_){
_start:
{
size_t v_sz_boxed_4180_; size_t v_i_boxed_4181_; lean_object* v_res_4182_; 
v_sz_boxed_4180_ = lean_unbox_usize(v_sz_4177_);
lean_dec(v_sz_4177_);
v_i_boxed_4181_ = lean_unbox_usize(v_i_4178_);
lean_dec(v_i_4178_);
v_res_4182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4180_, v_i_boxed_4181_, v_bs_4179_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4183_){
_start:
{
size_t v_sz_4184_; size_t v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_sz_4184_ = lean_array_size(v_a_4183_);
v___x_4185_ = ((size_t)0ULL);
v___x_4186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4184_, v___x_4185_, v_a_4183_);
v___x_4187_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4188_){
_start:
{
lean_object* v_identifier_4189_; lean_object* v_openNamespaces_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4210_; 
v_identifier_4189_ = lean_ctor_get(v_x_4188_, 0);
v_openNamespaces_4190_ = lean_ctor_get(v_x_4188_, 1);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_x_4188_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4192_ = v_x_4188_;
v_isShared_4193_ = v_isSharedCheck_4210_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_openNamespaces_4190_);
lean_inc(v_identifier_4189_);
lean_dec(v_x_4188_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4210_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4194_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4195_, 0, v_identifier_4189_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___x_4195_);
lean_ctor_set(v___x_4192_, 0, v___x_4194_);
v___x_4197_ = v___x_4192_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4198_ = lean_box(0);
v___x_4199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4201_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4190_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v___x_4198_);
v___x_4204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v___x_4198_);
v___x_4205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4199_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4207_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4205_, v___x_4206_);
v___x_4208_ = l_Lean_Json_mkObj(v___x_4207_);
lean_dec(v___x_4207_);
return v___x_4208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4216_, lean_object* v_k_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Lean_Json_getObjValD(v_j_4216_, v_k_4217_);
switch(lean_obj_tag(v___x_4218_))
{
case 3:
{
lean_object* v_s_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4227_; 
v_s_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_s_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
lean_ctor_set_tag(v___x_4221_, 0);
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_s_4219_);
v___x_4224_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
case 2:
{
lean_object* v_n_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4236_; 
v_n_4228_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4230_ = v___x_4218_;
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_n_4228_);
lean_dec(v___x_4218_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set_tag(v___x_4230_, 1);
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_n_4228_);
v___x_4233_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
return v___x_4234_;
}
}
}
default: 
{
lean_object* v___x_4237_; 
lean_dec(v___x_4218_);
v___x_4237_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4238_, lean_object* v_k_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4238_, v_k_4239_);
lean_dec_ref(v_k_4239_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4241_, size_t v_i_4242_, lean_object* v_bs_4243_){
_start:
{
uint8_t v___x_4244_; 
v___x_4244_ = lean_usize_dec_lt(v_i_4242_, v_sz_4241_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4245_, 0, v_bs_4243_);
return v___x_4245_;
}
else
{
lean_object* v_v_4246_; lean_object* v___x_4247_; 
v_v_4246_ = lean_array_uget_borrowed(v_bs_4243_, v_i_4242_);
lean_inc(v_v_4246_);
v___x_4247_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4246_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec_ref(v_bs_4243_);
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4247_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4247_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v_bs_x27_4258_; size_t v___x_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v_a_4256_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4257_ = lean_unsigned_to_nat(0u);
v_bs_x27_4258_ = lean_array_uset(v_bs_4243_, v_i_4242_, v___x_4257_);
v___x_4259_ = ((size_t)1ULL);
v___x_4260_ = lean_usize_add(v_i_4242_, v___x_4259_);
v___x_4261_ = lean_array_uset(v_bs_x27_4258_, v_i_4242_, v_a_4256_);
v_i_4242_ = v___x_4260_;
v_bs_4243_ = v___x_4261_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4263_, lean_object* v_i_4264_, lean_object* v_bs_4265_){
_start:
{
size_t v_sz_boxed_4266_; size_t v_i_boxed_4267_; lean_object* v_res_4268_; 
v_sz_boxed_4266_ = lean_unbox_usize(v_sz_4263_);
lean_dec(v_sz_4263_);
v_i_boxed_4267_ = lean_unbox_usize(v_i_4264_);
lean_dec(v_i_4264_);
v_res_4268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4266_, v_i_boxed_4267_, v_bs_4265_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4269_){
_start:
{
if (lean_obj_tag(v_x_4269_) == 4)
{
lean_object* v_elems_4270_; size_t v_sz_4271_; size_t v___x_4272_; lean_object* v___x_4273_; 
v_elems_4270_ = lean_ctor_get(v_x_4269_, 0);
lean_inc_ref(v_elems_4270_);
lean_dec_ref_known(v_x_4269_, 1);
v_sz_4271_ = lean_array_size(v_elems_4270_);
v___x_4272_ = ((size_t)0ULL);
v___x_4273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4271_, v___x_4272_, v_elems_4270_);
return v___x_4273_;
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4274_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4275_ = lean_unsigned_to_nat(80u);
v___x_4276_ = l_Lean_Json_pretty(v_x_4269_, v___x_4275_);
v___x_4277_ = lean_string_append(v___x_4274_, v___x_4276_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4279_ = lean_string_append(v___x_4277_, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4281_, lean_object* v_k_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = l_Lean_Json_getObjValD(v_j_4281_, v_k_4282_);
v___x_4284_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4283_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4285_, lean_object* v_k_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4285_, v_k_4286_);
lean_dec_ref(v_k_4286_);
return v_res_4287_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = 1;
v___x_4295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4295_, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4299_ = lean_string_append(v___x_4298_, v___x_4297_);
return v___x_4299_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = 1;
v___x_4303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4303_, v___x_4302_);
return v___x_4304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4307_ = lean_string_append(v___x_4306_, v___x_4305_);
return v___x_4307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4310_ = lean_string_append(v___x_4309_, v___x_4308_);
return v___x_4310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4314_ = 1;
v___x_4315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4315_, v___x_4314_);
return v___x_4316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4319_ = lean_string_append(v___x_4318_, v___x_4317_);
return v___x_4319_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4321_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4322_ = lean_string_append(v___x_4321_, v___x_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4323_);
v___x_4325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4323_, v___x_4324_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_json_4323_);
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4331_ = lean_string_append(v___x_4330_, v_a_4326_);
lean_dec(v_a_4326_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4331_);
v___x_4333_ = v___x_4328_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_json_4323_);
v_a_4336_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4325_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4325_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
lean_ctor_set_tag(v___x_4338_, 0);
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4344_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4325_, 1);
v___x_4345_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4323_, v___x_4345_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_a_4344_);
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4349_ = v___x_4346_;
v_isShared_4350_ = v_isSharedCheck_4356_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4356_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4352_ = lean_string_append(v___x_4351_, v_a_4347_);
lean_dec(v_a_4347_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4352_);
v___x_4354_ = v___x_4349_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
else
{
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_a_4344_);
v_a_4357_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4346_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4346_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 0);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4373_; 
v_a_4365_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4367_ = v___x_4346_;
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4346_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4373_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; lean_object* v___x_4371_; 
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_a_4344_);
lean_ctor_set(v___x_4369_, 1, v_a_4365_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4369_);
v___x_4371_ = v___x_4367_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4376_, size_t v_i_4377_, lean_object* v_bs_4378_){
_start:
{
uint8_t v___x_4379_; 
v___x_4379_ = lean_usize_dec_lt(v_i_4377_, v_sz_4376_);
if (v___x_4379_ == 0)
{
return v_bs_4378_;
}
else
{
lean_object* v_v_4380_; lean_object* v___x_4381_; lean_object* v_bs_x27_4382_; lean_object* v___x_4383_; size_t v___x_4384_; size_t v___x_4385_; lean_object* v___x_4386_; 
v_v_4380_ = lean_array_uget(v_bs_4378_, v_i_4377_);
v___x_4381_ = lean_unsigned_to_nat(0u);
v_bs_x27_4382_ = lean_array_uset(v_bs_4378_, v_i_4377_, v___x_4381_);
v___x_4383_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4380_);
v___x_4384_ = ((size_t)1ULL);
v___x_4385_ = lean_usize_add(v_i_4377_, v___x_4384_);
v___x_4386_ = lean_array_uset(v_bs_x27_4382_, v_i_4377_, v___x_4383_);
v_i_4377_ = v___x_4385_;
v_bs_4378_ = v___x_4386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4388_, lean_object* v_i_4389_, lean_object* v_bs_4390_){
_start:
{
size_t v_sz_boxed_4391_; size_t v_i_boxed_4392_; lean_object* v_res_4393_; 
v_sz_boxed_4391_ = lean_unbox_usize(v_sz_4388_);
lean_dec(v_sz_4388_);
v_i_boxed_4392_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4391_, v_i_boxed_4392_, v_bs_4390_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4394_){
_start:
{
size_t v_sz_4395_; size_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_sz_4395_ = lean_array_size(v_a_4394_);
v___x_4396_ = ((size_t)0ULL);
v___x_4397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4395_, v___x_4396_, v_a_4394_);
v___x_4398_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4399_){
_start:
{
lean_object* v_sourceRequestID_4400_; lean_object* v_queries_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4439_; 
v_sourceRequestID_4400_ = lean_ctor_get(v_x_4399_, 0);
v_queries_4401_ = lean_ctor_get(v_x_4399_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_x_4399_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4403_ = v_x_4399_;
v_isShared_4404_ = v_isSharedCheck_4439_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_queries_4401_);
lean_inc(v_sourceRequestID_4400_);
lean_dec(v_x_4399_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4439_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___y_4407_; 
v___x_4405_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4400_))
{
case 0:
{
lean_object* v_s_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
v_s_4422_ = lean_ctor_get(v_sourceRequestID_4400_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_sourceRequestID_4400_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v_sourceRequestID_4400_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_s_4422_);
lean_dec(v_sourceRequestID_4400_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
lean_ctor_set_tag(v___x_4424_, 3);
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_s_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
v___y_4407_ = v___x_4427_;
goto v___jp_4406_;
}
}
}
case 1:
{
lean_object* v_n_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_n_4430_ = lean_ctor_get(v_sourceRequestID_4400_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_sourceRequestID_4400_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v_sourceRequestID_4400_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_n_4430_);
lean_dec(v_sourceRequestID_4400_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set_tag(v___x_4432_, 2);
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_n_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
v___y_4407_ = v___x_4435_;
goto v___jp_4406_;
}
}
}
default: 
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_box(0);
v___y_4407_ = v___x_4438_;
goto v___jp_4406_;
}
}
v___jp_4406_:
{
lean_object* v___x_4409_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 1, v___y_4407_);
lean_ctor_set(v___x_4403_, 0, v___x_4405_);
v___x_4409_ = v___x_4403_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v___y_4407_);
v___x_4409_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4410_ = lean_box(0);
v___x_4411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4413_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4401_);
v___x_4414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
lean_ctor_set(v___x_4415_, 1, v___x_4410_);
v___x_4416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
lean_ctor_set(v___x_4416_, 1, v___x_4410_);
v___x_4417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4411_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4419_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4417_, v___x_4418_);
v___x_4420_ = l_Lean_Json_mkObj(v___x_4419_);
lean_dec(v___x_4419_);
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4442_, lean_object* v_k_4443_){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4444_ = l_Lean_Json_getObjValD(v_j_4442_, v_k_4443_);
v___x_4445_ = l_Lean_Name_fromJson_x3f(v___x_4444_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4446_, lean_object* v_k_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4446_, v_k_4447_);
lean_dec_ref(v_k_4447_);
return v_res_4448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = 1;
v___x_4456_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4457_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4456_, v___x_4455_);
return v___x_4457_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4459_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4460_ = lean_string_append(v___x_4459_, v___x_4458_);
return v___x_4460_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = 1;
v___x_4464_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4464_, v___x_4463_);
return v___x_4465_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4467_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4468_ = lean_string_append(v___x_4467_, v___x_4466_);
return v___x_4468_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4470_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4471_ = lean_string_append(v___x_4470_, v___x_4469_);
return v___x_4471_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = 1;
v___x_4476_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4476_, v___x_4475_);
return v___x_4477_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4479_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4480_ = lean_string_append(v___x_4479_, v___x_4478_);
return v___x_4480_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4481_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4483_ = lean_string_append(v___x_4482_, v___x_4481_);
return v___x_4483_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4487_ = 1;
v___x_4488_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4488_, v___x_4487_);
return v___x_4489_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4491_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4492_ = lean_string_append(v___x_4491_, v___x_4490_);
return v___x_4492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4493_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4494_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4495_ = lean_string_append(v___x_4494_, v___x_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4496_){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4496_);
v___x_4498_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4496_, v___x_4497_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_json_4496_);
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4501_ = v___x_4498_;
v_isShared_4502_ = v_isSharedCheck_4508_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4508_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4504_ = lean_string_append(v___x_4503_, v_a_4499_);
lean_dec(v_a_4499_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4504_);
v___x_4506_ = v___x_4501_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
else
{
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_json_4496_);
v_a_4509_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4498_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4498_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set_tag(v___x_4511_, 0);
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v_a_4517_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4496_);
v___x_4519_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4496_, v___x_4518_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4529_; 
lean_dec(v_a_4517_);
lean_dec(v_json_4496_);
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4522_ = v___x_4519_;
v_isShared_4523_ = v_isSharedCheck_4529_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4529_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4527_; 
v___x_4524_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4525_ = lean_string_append(v___x_4524_, v_a_4520_);
lean_dec(v_a_4520_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4525_);
v___x_4527_ = v___x_4522_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
else
{
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_a_4517_);
lean_dec(v_json_4496_);
v_a_4530_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4519_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4519_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set_tag(v___x_4532_, 0);
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v_a_4538_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4519_, 1);
v___x_4539_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4540_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4496_, v___x_4539_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v_a_4538_);
lean_dec(v_a_4517_);
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4550_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4550_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v___x_4545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4546_ = lean_string_append(v___x_4545_, v_a_4541_);
lean_dec(v_a_4541_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4546_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
else
{
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_a_4538_);
lean_dec(v_a_4517_);
v_a_4551_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4540_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4540_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set_tag(v___x_4553_, 0);
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4568_; 
v_a_4559_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4561_ = v___x_4540_;
v_isShared_4562_ = v_isSharedCheck_4568_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4540_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4568_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4566_; 
v___x_4563_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4563_, 0, v_a_4517_);
lean_ctor_set(v___x_4563_, 1, v_a_4538_);
v___x_4564_ = lean_unbox(v_a_4559_);
lean_dec(v_a_4559_);
lean_ctor_set_uint8(v___x_4563_, sizeof(void*)*2, v___x_4564_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4563_);
v___x_4566_ = v___x_4561_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v___x_4563_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4571_){
_start:
{
lean_object* v_module_4572_; lean_object* v_decl_4573_; uint8_t v_isExactMatch_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v_module_4572_ = lean_ctor_get(v_x_4571_, 0);
lean_inc(v_module_4572_);
v_decl_4573_ = lean_ctor_get(v_x_4571_, 1);
lean_inc(v_decl_4573_);
v_isExactMatch_4574_ = lean_ctor_get_uint8(v_x_4571_, sizeof(void*)*2);
lean_dec_ref(v_x_4571_);
v___x_4575_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4576_ = 1;
v___x_4577_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4572_, v___x_4576_);
v___x_4578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4575_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
v___x_4580_ = lean_box(0);
v___x_4581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4579_);
lean_ctor_set(v___x_4581_, 1, v___x_4580_);
v___x_4582_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4583_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4573_, v___x_4576_);
v___x_4584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4582_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
lean_ctor_set(v___x_4586_, 1, v___x_4580_);
v___x_4587_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4588_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4588_, 0, v_isExactMatch_4574_);
v___x_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
lean_ctor_set(v___x_4590_, 1, v___x_4580_);
v___x_4591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
lean_ctor_set(v___x_4591_, 1, v___x_4580_);
v___x_4592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4586_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4581_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4595_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4593_, v___x_4594_);
v___x_4596_ = l_Lean_Json_mkObj(v___x_4595_);
lean_dec(v___x_4595_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4599_, size_t v_i_4600_, lean_object* v_bs_4601_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_lt(v_i_4600_, v_sz_4599_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_bs_4601_);
return v___x_4603_;
}
else
{
lean_object* v_v_4604_; lean_object* v___x_4605_; 
v_v_4604_ = lean_array_uget_borrowed(v_bs_4601_, v_i_4600_);
lean_inc(v_v_4604_);
v___x_4605_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4604_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v_bs_4601_);
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4605_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4615_; lean_object* v_bs_x27_4616_; size_t v___x_4617_; size_t v___x_4618_; lean_object* v___x_4619_; 
v_a_4614_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4614_);
lean_dec_ref_known(v___x_4605_, 1);
v___x_4615_ = lean_unsigned_to_nat(0u);
v_bs_x27_4616_ = lean_array_uset(v_bs_4601_, v_i_4600_, v___x_4615_);
v___x_4617_ = ((size_t)1ULL);
v___x_4618_ = lean_usize_add(v_i_4600_, v___x_4617_);
v___x_4619_ = lean_array_uset(v_bs_x27_4616_, v_i_4600_, v_a_4614_);
v_i_4600_ = v___x_4618_;
v_bs_4601_ = v___x_4619_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4621_, lean_object* v_i_4622_, lean_object* v_bs_4623_){
_start:
{
size_t v_sz_boxed_4624_; size_t v_i_boxed_4625_; lean_object* v_res_4626_; 
v_sz_boxed_4624_ = lean_unbox_usize(v_sz_4621_);
lean_dec(v_sz_4621_);
v_i_boxed_4625_ = lean_unbox_usize(v_i_4622_);
lean_dec(v_i_4622_);
v_res_4626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4624_, v_i_boxed_4625_, v_bs_4623_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4627_){
_start:
{
if (lean_obj_tag(v_x_4627_) == 4)
{
lean_object* v_elems_4628_; size_t v_sz_4629_; size_t v___x_4630_; lean_object* v___x_4631_; 
v_elems_4628_ = lean_ctor_get(v_x_4627_, 0);
lean_inc_ref(v_elems_4628_);
lean_dec_ref_known(v_x_4627_, 1);
v_sz_4629_ = lean_array_size(v_elems_4628_);
v___x_4630_ = ((size_t)0ULL);
v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4629_, v___x_4630_, v_elems_4628_);
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4632_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4633_ = lean_unsigned_to_nat(80u);
v___x_4634_ = l_Lean_Json_pretty(v_x_4627_, v___x_4633_);
v___x_4635_ = lean_string_append(v___x_4632_, v___x_4634_);
lean_dec_ref(v___x_4634_);
v___x_4636_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4637_ = lean_string_append(v___x_4635_, v___x_4636_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4639_, size_t v_i_4640_, lean_object* v_bs_4641_){
_start:
{
uint8_t v___x_4642_; 
v___x_4642_ = lean_usize_dec_lt(v_i_4640_, v_sz_4639_);
if (v___x_4642_ == 0)
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4643_, 0, v_bs_4641_);
return v___x_4643_;
}
else
{
lean_object* v_v_4644_; lean_object* v___x_4645_; 
v_v_4644_ = lean_array_uget_borrowed(v_bs_4641_, v_i_4640_);
lean_inc(v_v_4644_);
v___x_4645_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4644_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec_ref(v_bs_4641_);
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4645_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4655_; lean_object* v_bs_x27_4656_; size_t v___x_4657_; size_t v___x_4658_; lean_object* v___x_4659_; 
v_a_4654_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4655_ = lean_unsigned_to_nat(0u);
v_bs_x27_4656_ = lean_array_uset(v_bs_4641_, v_i_4640_, v___x_4655_);
v___x_4657_ = ((size_t)1ULL);
v___x_4658_ = lean_usize_add(v_i_4640_, v___x_4657_);
v___x_4659_ = lean_array_uset(v_bs_x27_4656_, v_i_4640_, v_a_4654_);
v_i_4640_ = v___x_4658_;
v_bs_4641_ = v___x_4659_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4661_, lean_object* v_i_4662_, lean_object* v_bs_4663_){
_start:
{
size_t v_sz_boxed_4664_; size_t v_i_boxed_4665_; lean_object* v_res_4666_; 
v_sz_boxed_4664_ = lean_unbox_usize(v_sz_4661_);
lean_dec(v_sz_4661_);
v_i_boxed_4665_ = lean_unbox_usize(v_i_4662_);
lean_dec(v_i_4662_);
v_res_4666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4664_, v_i_boxed_4665_, v_bs_4663_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4667_){
_start:
{
if (lean_obj_tag(v_x_4667_) == 4)
{
lean_object* v_elems_4668_; size_t v_sz_4669_; size_t v___x_4670_; lean_object* v___x_4671_; 
v_elems_4668_ = lean_ctor_get(v_x_4667_, 0);
lean_inc_ref(v_elems_4668_);
lean_dec_ref_known(v_x_4667_, 1);
v_sz_4669_ = lean_array_size(v_elems_4668_);
v___x_4670_ = ((size_t)0ULL);
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4669_, v___x_4670_, v_elems_4668_);
return v___x_4671_;
}
else
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4672_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4673_ = lean_unsigned_to_nat(80u);
v___x_4674_ = l_Lean_Json_pretty(v_x_4667_, v___x_4673_);
v___x_4675_ = lean_string_append(v___x_4672_, v___x_4674_);
lean_dec_ref(v___x_4674_);
v___x_4676_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4677_ = lean_string_append(v___x_4675_, v___x_4676_);
v___x_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
return v___x_4678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4679_, lean_object* v_k_4680_){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = l_Lean_Json_getObjValD(v_j_4679_, v_k_4680_);
v___x_4682_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4683_, lean_object* v_k_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4683_, v_k_4684_);
lean_dec_ref(v_k_4684_);
return v_res_4685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4692_ = 1;
v___x_4693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4693_, v___x_4692_);
return v___x_4694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4695_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4697_ = lean_string_append(v___x_4696_, v___x_4695_);
return v___x_4697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4700_ = 1;
v___x_4701_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4702_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4701_, v___x_4700_);
return v___x_4702_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4705_ = lean_string_append(v___x_4704_, v___x_4703_);
return v___x_4705_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4707_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4708_ = lean_string_append(v___x_4707_, v___x_4706_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4709_){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4711_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4709_, v___x_4710_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4721_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4721_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4721_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4717_ = lean_string_append(v___x_4716_, v_a_4712_);
lean_dec(v_a_4712_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v___x_4717_);
v___x_4719_ = v___x_4714_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
else
{
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
v_a_4722_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4711_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4711_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 0);
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
v_a_4730_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4711_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4711_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4740_, size_t v_i_4741_, lean_object* v_bs_4742_){
_start:
{
uint8_t v___x_4743_; 
v___x_4743_ = lean_usize_dec_lt(v_i_4741_, v_sz_4740_);
if (v___x_4743_ == 0)
{
return v_bs_4742_;
}
else
{
lean_object* v_v_4744_; lean_object* v___x_4745_; lean_object* v_bs_x27_4746_; lean_object* v___x_4747_; size_t v___x_4748_; size_t v___x_4749_; lean_object* v___x_4750_; 
v_v_4744_ = lean_array_uget(v_bs_4742_, v_i_4741_);
v___x_4745_ = lean_unsigned_to_nat(0u);
v_bs_x27_4746_ = lean_array_uset(v_bs_4742_, v_i_4741_, v___x_4745_);
v___x_4747_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4744_);
v___x_4748_ = ((size_t)1ULL);
v___x_4749_ = lean_usize_add(v_i_4741_, v___x_4748_);
v___x_4750_ = lean_array_uset(v_bs_x27_4746_, v_i_4741_, v___x_4747_);
v_i_4741_ = v___x_4749_;
v_bs_4742_ = v___x_4750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4752_, lean_object* v_i_4753_, lean_object* v_bs_4754_){
_start:
{
size_t v_sz_boxed_4755_; size_t v_i_boxed_4756_; lean_object* v_res_4757_; 
v_sz_boxed_4755_ = lean_unbox_usize(v_sz_4752_);
lean_dec(v_sz_4752_);
v_i_boxed_4756_ = lean_unbox_usize(v_i_4753_);
lean_dec(v_i_4753_);
v_res_4757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4755_, v_i_boxed_4756_, v_bs_4754_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4758_){
_start:
{
size_t v_sz_4759_; size_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v_sz_4759_ = lean_array_size(v_a_4758_);
v___x_4760_ = ((size_t)0ULL);
v___x_4761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4759_, v___x_4760_, v_a_4758_);
v___x_4762_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4763_, size_t v_i_4764_, lean_object* v_bs_4765_){
_start:
{
uint8_t v___x_4766_; 
v___x_4766_ = lean_usize_dec_lt(v_i_4764_, v_sz_4763_);
if (v___x_4766_ == 0)
{
return v_bs_4765_;
}
else
{
lean_object* v_v_4767_; lean_object* v___x_4768_; lean_object* v_bs_x27_4769_; lean_object* v___x_4770_; size_t v___x_4771_; size_t v___x_4772_; lean_object* v___x_4773_; 
v_v_4767_ = lean_array_uget(v_bs_4765_, v_i_4764_);
v___x_4768_ = lean_unsigned_to_nat(0u);
v_bs_x27_4769_ = lean_array_uset(v_bs_4765_, v_i_4764_, v___x_4768_);
v___x_4770_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4767_);
v___x_4771_ = ((size_t)1ULL);
v___x_4772_ = lean_usize_add(v_i_4764_, v___x_4771_);
v___x_4773_ = lean_array_uset(v_bs_x27_4769_, v_i_4764_, v___x_4770_);
v_i_4764_ = v___x_4772_;
v_bs_4765_ = v___x_4773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4775_, lean_object* v_i_4776_, lean_object* v_bs_4777_){
_start:
{
size_t v_sz_boxed_4778_; size_t v_i_boxed_4779_; lean_object* v_res_4780_; 
v_sz_boxed_4778_ = lean_unbox_usize(v_sz_4775_);
lean_dec(v_sz_4775_);
v_i_boxed_4779_ = lean_unbox_usize(v_i_4776_);
lean_dec(v_i_4776_);
v_res_4780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4778_, v_i_boxed_4779_, v_bs_4777_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4781_){
_start:
{
size_t v_sz_4782_; size_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v_sz_4782_ = lean_array_size(v_a_4781_);
v___x_4783_ = ((size_t)0ULL);
v___x_4784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4782_, v___x_4783_, v_a_4781_);
v___x_4785_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4786_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4787_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4788_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4786_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = lean_box(0);
v___x_4791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4789_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v___x_4792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
lean_ctor_set(v___x_4792_, 1, v___x_4790_);
v___x_4793_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4794_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4792_, v___x_4793_);
v___x_4795_ = l_Lean_Json_mkObj(v___x_4794_);
lean_dec(v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4807_ = 1;
v___x_4808_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4808_, v___x_4807_);
return v___x_4809_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4810_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4811_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4812_ = lean_string_append(v___x_4811_, v___x_4810_);
return v___x_4812_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4815_ = lean_string_append(v___x_4814_, v___x_4813_);
return v___x_4815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4816_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4818_ = lean_string_append(v___x_4817_, v___x_4816_);
return v___x_4818_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4821_ = lean_string_append(v___x_4820_, v___x_4819_);
return v___x_4821_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4822_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4823_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4824_ = lean_string_append(v___x_4823_, v___x_4822_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4825_){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4825_);
v___x_4827_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4825_, v___x_4826_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4837_; 
lean_dec(v_json_4825_);
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4830_ = v___x_4827_;
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4827_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4837_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4835_; 
v___x_4832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4833_ = lean_string_append(v___x_4832_, v_a_4828_);
lean_dec(v_a_4828_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v___x_4833_);
v___x_4835_ = v___x_4830_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
lean_dec(v_json_4825_);
v_a_4838_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4827_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4827_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
lean_ctor_set_tag(v___x_4840_, 0);
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v_a_4846_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4846_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4848_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4825_, v___x_4847_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4858_; 
lean_dec(v_a_4846_);
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4858_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4858_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4854_ = lean_string_append(v___x_4853_, v_a_4849_);
lean_dec(v_a_4849_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4854_);
v___x_4856_ = v___x_4851_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
else
{
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
lean_dec(v_a_4846_);
v_a_4859_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4848_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4848_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
lean_ctor_set_tag(v___x_4861_, 0);
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4875_; 
v_a_4867_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4869_ = v___x_4848_;
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4848_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4871_, 0, v_a_4846_);
lean_ctor_set(v___x_4871_, 1, v_a_4867_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4871_);
v___x_4873_ = v___x_4869_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4878_){
_start:
{
lean_object* v_module_4879_; lean_object* v_decl_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4903_; 
v_module_4879_ = lean_ctor_get(v_x_4878_, 0);
v_decl_4880_ = lean_ctor_get(v_x_4878_, 1);
v_isSharedCheck_4903_ = !lean_is_exclusive(v_x_4878_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4882_ = v_x_4878_;
v_isShared_4883_ = v_isSharedCheck_4903_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_decl_4880_);
lean_inc(v_module_4879_);
lean_dec(v_x_4878_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4903_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4884_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4885_ = 1;
v___x_4886_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4879_, v___x_4885_);
v___x_4887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 1, v___x_4887_);
lean_ctor_set(v___x_4882_, 0, v___x_4884_);
v___x_4889_ = v___x_4882_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4890_ = lean_box(0);
v___x_4891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4889_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4893_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4880_, v___x_4885_);
v___x_4894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4892_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
lean_ctor_set(v___x_4896_, 1, v___x_4890_);
v___x_4897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
lean_ctor_set(v___x_4897_, 1, v___x_4890_);
v___x_4898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4891_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
v___x_4899_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4900_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4898_, v___x_4899_);
v___x_4901_ = l_Lean_Json_mkObj(v___x_4900_);
lean_dec(v___x_4900_);
return v___x_4901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4906_, lean_object* v_k_4907_){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = l_Lean_Json_getObjValD(v_j_4906_, v_k_4907_);
v___x_4909_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4910_, lean_object* v_k_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4910_, v_k_4911_);
lean_dec_ref(v_k_4911_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4915_){
_start:
{
if (lean_obj_tag(v_x_4915_) == 0)
{
lean_object* v___x_4916_; 
v___x_4916_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4916_;
}
else
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4915_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4934_; 
v_a_4926_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4928_ = v___x_4917_;
v_isShared_4929_ = v_isSharedCheck_4934_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4917_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4934_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_a_4926_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4930_);
v___x_4932_ = v___x_4928_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4930_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4935_, lean_object* v_k_4936_){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = l_Lean_Json_getObjValD(v_j_4935_, v_k_4936_);
v___x_4938_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4939_, lean_object* v_k_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4939_, v_k_4940_);
lean_dec_ref(v_k_4940_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4944_){
_start:
{
if (lean_obj_tag(v_x_4944_) == 0)
{
lean_object* v___x_4945_; 
v___x_4945_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4945_;
}
else
{
lean_object* v___x_4946_; 
v___x_4946_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4944_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4946_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
else
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4963_; 
v_a_4955_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4957_ = v___x_4946_;
v_isShared_4958_ = v_isSharedCheck_4963_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4946_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4963_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4959_; lean_object* v___x_4961_; 
v___x_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4959_, 0, v_a_4955_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 0, v___x_4959_);
v___x_4961_ = v___x_4957_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4959_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4964_, lean_object* v_k_4965_){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = l_Lean_Json_getObjValD(v_j_4964_, v_k_4965_);
v___x_4967_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4966_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4968_, lean_object* v_k_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4968_, v_k_4969_);
lean_dec_ref(v_k_4969_);
return v_res_4970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4977_ = 1;
v___x_4978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4978_, v___x_4977_);
return v___x_4979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4982_ = lean_string_append(v___x_4981_, v___x_4980_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = 1;
v___x_4987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4987_, v___x_4986_);
return v___x_4988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4989_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4991_ = lean_string_append(v___x_4990_, v___x_4989_);
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4994_ = lean_string_append(v___x_4993_, v___x_4992_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4998_ = 1;
v___x_4999_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_5000_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4999_, v___x_4998_);
return v___x_5000_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_5002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5003_ = lean_string_append(v___x_5002_, v___x_5001_);
return v___x_5003_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_5006_ = lean_string_append(v___x_5005_, v___x_5004_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = 1;
v___x_5011_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_5012_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5011_, v___x_5010_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_5014_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5015_ = lean_string_append(v___x_5014_, v___x_5013_);
return v___x_5015_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5016_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5017_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_5018_ = lean_string_append(v___x_5017_, v___x_5016_);
return v___x_5018_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5022_ = 1;
v___x_5023_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_5024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5023_, v___x_5022_);
return v___x_5024_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_5026_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5027_ = lean_string_append(v___x_5026_, v___x_5025_);
return v___x_5027_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_5030_ = lean_string_append(v___x_5029_, v___x_5028_);
return v___x_5030_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5035_ = 1;
v___x_5036_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_5037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5036_, v___x_5035_);
return v___x_5037_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5038_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_5039_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5040_ = lean_string_append(v___x_5039_, v___x_5038_);
return v___x_5040_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5041_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5042_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5043_ = lean_string_append(v___x_5042_, v___x_5041_);
return v___x_5043_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = 1;
v___x_5048_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5049_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5048_, v___x_5047_);
return v___x_5049_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5050_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5051_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5052_ = lean_string_append(v___x_5051_, v___x_5050_);
return v___x_5052_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5053_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5054_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5055_ = lean_string_append(v___x_5054_, v___x_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5056_){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5056_);
v___x_5058_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5056_, v___x_5057_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5068_; 
lean_dec(v_json_5056_);
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5061_ = v___x_5058_;
v_isShared_5062_ = v_isSharedCheck_5068_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5058_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5068_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5066_; 
v___x_5063_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5064_ = lean_string_append(v___x_5063_, v_a_5059_);
lean_dec(v_a_5059_);
if (v_isShared_5062_ == 0)
{
lean_ctor_set(v___x_5061_, 0, v___x_5064_);
v___x_5066_ = v___x_5061_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5064_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
else
{
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_dec(v_json_5056_);
v_a_5069_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5058_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5058_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set_tag(v___x_5071_, 0);
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v_a_5077_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5056_);
v___x_5079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5056_, v___x_5078_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5089_; 
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5082_ = v___x_5079_;
v_isShared_5083_ = v_isSharedCheck_5089_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5079_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5089_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5085_ = lean_string_append(v___x_5084_, v_a_5080_);
lean_dec(v_a_5080_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 0, v___x_5085_);
v___x_5087_ = v___x_5082_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5085_);
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
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5090_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5079_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5079_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set_tag(v___x_5092_, 0);
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
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
lean_object* v_a_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v_a_5098_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5079_, 1);
v___x_5099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5056_);
v___x_5100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5056_, v___x_5099_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5110_; 
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5110_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5110_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
v___x_5105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5106_ = lean_string_append(v___x_5105_, v_a_5101_);
lean_dec(v_a_5101_);
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 0, v___x_5106_);
v___x_5108_ = v___x_5103_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
else
{
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5111_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5100_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5100_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
lean_ctor_set_tag(v___x_5113_, 0);
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
v_a_5119_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5119_);
lean_dec_ref_known(v___x_5100_, 1);
v___x_5120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5056_);
v___x_5121_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5056_, v___x_5120_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5131_; 
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5124_ = v___x_5121_;
v_isShared_5125_ = v_isSharedCheck_5131_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5121_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5131_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5129_; 
v___x_5126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5127_ = lean_string_append(v___x_5126_, v_a_5122_);
lean_dec(v_a_5122_);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v___x_5127_);
v___x_5129_ = v___x_5124_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5127_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
else
{
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5132_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5121_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5121_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set_tag(v___x_5134_, 0);
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v_a_5140_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5121_, 1);
v___x_5141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5056_);
v___x_5142_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5056_, v___x_5141_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_a_5140_);
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5145_ = v___x_5142_;
v_isShared_5146_ = v_isSharedCheck_5152_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5152_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5148_ = lean_string_append(v___x_5147_, v_a_5143_);
lean_dec(v_a_5143_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v___x_5148_);
v___x_5150_ = v___x_5145_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
else
{
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
lean_dec(v_a_5140_);
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_json_5056_);
v_a_5153_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5142_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5142_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
lean_ctor_set_tag(v___x_5155_, 0);
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v_a_5161_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_a_5161_);
lean_dec_ref_known(v___x_5142_, 1);
v___x_5162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5163_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5056_, v___x_5162_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5173_; 
lean_dec(v_a_5161_);
lean_dec(v_a_5140_);
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5166_ = v___x_5163_;
v_isShared_5167_ = v_isSharedCheck_5173_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5163_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5173_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5171_; 
v___x_5168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5169_ = lean_string_append(v___x_5168_, v_a_5164_);
lean_dec(v_a_5164_);
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 0, v___x_5169_);
v___x_5171_ = v___x_5166_;
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
else
{
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_dec(v_a_5161_);
lean_dec(v_a_5140_);
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
v_a_5174_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5163_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5163_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
lean_ctor_set_tag(v___x_5176_, 0);
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5192_; 
v_a_5182_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5184_ = v___x_5163_;
v_isShared_5185_ = v_isSharedCheck_5192_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5163_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5192_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; uint8_t v___x_5188_; lean_object* v___x_5190_; 
v___x_5186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5186_, 0, v_a_5077_);
lean_ctor_set(v___x_5186_, 1, v_a_5098_);
lean_ctor_set(v___x_5186_, 2, v_a_5119_);
lean_ctor_set(v___x_5186_, 3, v_a_5140_);
v___x_5187_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
lean_ctor_set(v___x_5187_, 1, v_a_5161_);
v___x_5188_ = lean_unbox(v_a_5182_);
lean_dec(v_a_5182_);
lean_ctor_set_uint8(v___x_5187_, sizeof(void*)*2, v___x_5188_);
if (v_isShared_5185_ == 0)
{
lean_ctor_set(v___x_5184_, 0, v___x_5187_);
v___x_5190_ = v___x_5184_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5187_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5195_, lean_object* v_x_5196_){
_start:
{
if (lean_obj_tag(v_x_5196_) == 0)
{
lean_object* v___x_5197_; 
lean_dec_ref(v_k_5195_);
v___x_5197_ = lean_box(0);
return v___x_5197_;
}
else
{
lean_object* v_val_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v_val_5198_ = lean_ctor_get(v_x_5196_, 0);
lean_inc(v_val_5198_);
lean_dec_ref_known(v_x_5196_, 1);
v___x_5199_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5198_);
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v_k_5195_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = lean_box(0);
v___x_5202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5200_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5203_, lean_object* v_x_5204_){
_start:
{
if (lean_obj_tag(v_x_5204_) == 0)
{
lean_object* v___x_5205_; 
lean_dec_ref(v_k_5203_);
v___x_5205_ = lean_box(0);
return v___x_5205_;
}
else
{
lean_object* v_val_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v_val_5206_ = lean_ctor_get(v_x_5204_, 0);
lean_inc(v_val_5206_);
lean_dec_ref_known(v_x_5204_, 1);
v___x_5207_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5206_);
v___x_5208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5208_, 0, v_k_5203_);
lean_ctor_set(v___x_5208_, 1, v___x_5207_);
v___x_5209_ = lean_box(0);
v___x_5210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5208_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
return v___x_5210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5211_){
_start:
{
lean_object* v_toLocationLink_5212_; lean_object* v_ident_x3f_5213_; uint8_t v_isDefault_5214_; lean_object* v_originSelectionRange_x3f_5215_; lean_object* v_targetUri_5216_; lean_object* v_targetRange_5217_; lean_object* v_targetSelectionRange_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v_toLocationLink_5212_ = lean_ctor_get(v_x_5211_, 0);
lean_inc_ref(v_toLocationLink_5212_);
v_ident_x3f_5213_ = lean_ctor_get(v_x_5211_, 1);
lean_inc(v_ident_x3f_5213_);
v_isDefault_5214_ = lean_ctor_get_uint8(v_x_5211_, sizeof(void*)*2);
lean_dec_ref(v_x_5211_);
v_originSelectionRange_x3f_5215_ = lean_ctor_get(v_toLocationLink_5212_, 0);
lean_inc(v_originSelectionRange_x3f_5215_);
v_targetUri_5216_ = lean_ctor_get(v_toLocationLink_5212_, 1);
lean_inc_ref(v_targetUri_5216_);
v_targetRange_5217_ = lean_ctor_get(v_toLocationLink_5212_, 2);
lean_inc_ref(v_targetRange_5217_);
v_targetSelectionRange_5218_ = lean_ctor_get(v_toLocationLink_5212_, 3);
lean_inc_ref(v_targetSelectionRange_5218_);
lean_dec_ref(v_toLocationLink_5212_);
v___x_5219_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5220_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5219_, v_originSelectionRange_x3f_5215_);
v___x_5221_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5222_, 0, v_targetUri_5216_);
v___x_5223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5221_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
v___x_5224_ = lean_box(0);
v___x_5225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
v___x_5226_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5227_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5217_);
v___x_5228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5226_);
lean_ctor_set(v___x_5228_, 1, v___x_5227_);
v___x_5229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5228_);
lean_ctor_set(v___x_5229_, 1, v___x_5224_);
v___x_5230_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5231_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5218_);
v___x_5232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5230_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
lean_ctor_set(v___x_5233_, 1, v___x_5224_);
v___x_5234_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5235_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5234_, v_ident_x3f_5213_);
v___x_5236_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5237_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5237_, 0, v_isDefault_5214_);
v___x_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5236_);
lean_ctor_set(v___x_5238_, 1, v___x_5237_);
v___x_5239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
lean_ctor_set(v___x_5239_, 1, v___x_5224_);
v___x_5240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5239_);
lean_ctor_set(v___x_5240_, 1, v___x_5224_);
v___x_5241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5235_);
lean_ctor_set(v___x_5241_, 1, v___x_5240_);
v___x_5242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5233_);
lean_ctor_set(v___x_5242_, 1, v___x_5241_);
v___x_5243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5229_);
lean_ctor_set(v___x_5243_, 1, v___x_5242_);
v___x_5244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5225_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5220_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5247_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5245_, v___x_5246_);
v___x_5248_ = l_Lean_Json_mkObj(v___x_5247_);
lean_dec(v___x_5247_);
return v___x_5248_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
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

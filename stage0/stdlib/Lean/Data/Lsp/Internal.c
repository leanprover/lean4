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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
lean_object* v_elems_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_699_; 
v_elems_581_ = lean_ctor_get(v_x_580_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_699_ == 0)
{
v___x_583_ = v_x_580_;
v_isShared_584_ = v_isSharedCheck_699_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_elems_581_);
lean_dec(v_x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_699_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_585_ = lean_array_get_size(v_elems_581_);
v___x_586_ = lean_unsigned_to_nat(8u);
v___x_587_ = lean_nat_dec_eq(v___x_585_, v___x_586_);
v___x_588_ = lean_bool_not(v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_del_object(v___x_583_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_589_);
lean_inc(v___x_590_);
v___x_591_ = l_Lean_Json_getNat_x3f(v___x_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_elems_581_);
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_600_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_591_, 1);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_601_);
lean_inc(v___x_602_);
v___x_603_ = l_Lean_Json_getNat_x3f(v___x_602_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_a_612_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_603_, 1);
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_613_);
lean_inc(v___x_614_);
v___x_615_ = l_Lean_Json_getNat_x3f(v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_612_);
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_615_, 1);
v___x_625_ = lean_unsigned_to_nat(3u);
v___x_626_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_625_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Json_getNat_x3f(v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_a_636_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_627_, 1);
v___x_637_ = lean_unsigned_to_nat(4u);
v___x_638_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_637_);
lean_inc(v___x_638_);
v___x_639_ = l_Lean_Json_getNat_x3f(v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_648_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_639_, 1);
v___x_649_ = lean_unsigned_to_nat(5u);
v___x_650_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_649_);
lean_inc(v___x_650_);
v___x_651_ = l_Lean_Json_getNat_x3f(v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_660_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_651_, 1);
v___x_661_ = lean_unsigned_to_nat(6u);
v___x_662_ = lean_array_get_borrowed(v___x_579_, v_elems_581_, v___x_661_);
lean_inc(v___x_662_);
v___x_663_ = l_Lean_Json_getNat_x3f(v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_660_);
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec(v_a_600_);
lean_dec_ref(v_elems_581_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_672_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_663_, 1);
v___x_673_ = lean_unsigned_to_nat(7u);
v___x_674_ = lean_array_get(v___x_579_, v_elems_581_, v___x_673_);
lean_dec_ref(v_elems_581_);
v___x_675_ = l_Lean_Json_getNat_x3f(v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_a_672_);
lean_dec(v_a_660_);
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec(v_a_600_);
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_675_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_688_, 0, v_a_600_);
lean_ctor_set(v___x_688_, 1, v_a_612_);
lean_ctor_set(v___x_688_, 2, v_a_624_);
lean_ctor_set(v___x_688_, 3, v_a_636_);
lean_ctor_set(v___x_688_, 4, v_a_648_);
lean_ctor_set(v___x_688_, 5, v_a_660_);
lean_ctor_set(v___x_688_, 6, v_a_672_);
lean_ctor_set(v___x_688_, 7, v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
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
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec_ref(v_elems_581_);
v___x_693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_694_ = l_Nat_reprFast(v___x_585_);
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_dec_ref(v___x_694_);
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
lean_ctor_set(v___x_583_, 0, v___x_695_);
v___x_697_ = v___x_583_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v___x_700_; 
lean_dec(v_x_580_);
v___x_700_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object* v___x_701_, lean_object* v_x_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Lsp_instFromJsonDeclInfo___lam__0(v___x_701_, v_x_702_);
lean_dec(v___x_701_);
return v_res_703_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(1);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(1);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_709_, lean_object* v_a_710_, lean_object* v_b_711_, lean_object* v_c_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_710_);
lean_ctor_set(v___x_713_, 1, v_b_711_);
v___x_714_ = lean_apply_2(v_f_709_, v___x_713_, v_c_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_734_, lean_object* v_init_735_, lean_object* v_f_736_){
_start:
{
lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_a_740_; 
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_737_, 0, v_f_736_);
v___x_738_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_739_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_738_, v___f_737_, v_init_735_, v_m_734_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec(v___x_739_);
return v_a_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_init_743_, lean_object* v_f_744_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_a_748_; 
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_745_, 0, v_f_744_);
v___x_746_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_747_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_746_, v___f_745_, v_init_743_, v_m_742_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec(v___x_747_);
return v_a_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_749_, lean_object* v_init_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v_k_752_; lean_object* v_v_753_; lean_object* v_l_754_; lean_object* v_r_755_; lean_object* v___x_756_; 
v_k_752_ = lean_ctor_get(v_x_751_, 1);
v_v_753_ = lean_ctor_get(v_x_751_, 2);
v_l_754_ = lean_ctor_get(v_x_751_, 3);
v_r_755_ = lean_ctor_get(v_x_751_, 4);
lean_inc_ref(v___y_749_);
v___x_756_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_749_, v_init_750_, v_l_754_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_dec_ref(v___y_749_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
lean_inc(v_v_753_);
lean_inc(v_k_752_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_k_752_);
lean_ctor_set(v___x_758_, 1, v_v_753_);
lean_inc_ref(v___y_749_);
v___x_759_ = lean_apply_2(v___y_749_, v___x_758_, v_a_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_dec_ref(v___y_749_);
return v___x_759_;
}
else
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v_init_750_ = v_a_760_;
v_x_751_ = v_r_755_;
goto _start;
}
}
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v___y_749_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_init_750_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_763_, lean_object* v_init_764_, lean_object* v_x_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_763_, v_init_764_, v_x_765_);
lean_dec(v_x_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_771_; lean_object* v_a_772_; 
v___x_771_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_770_, v___y_769_, v___y_768_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
return v_a_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v_init_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_781_, v_init_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v_init_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_785_, v___y_786_, v_init_787_, v_x_788_);
lean_dec(v_x_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_790_){
_start:
{
lean_object* v_snd_791_; lean_object* v_fst_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_834_; 
v_snd_791_ = lean_ctor_get(v_x_790_, 1);
v_fst_792_ = lean_ctor_get(v_x_790_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_790_);
if (v_isSharedCheck_834_ == 0)
{
v___x_794_ = v_x_790_;
v_isShared_795_ = v_isSharedCheck_834_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_792_);
lean_dec(v_x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_834_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_rangeStartPosLine_796_; lean_object* v_rangeStartPosCharacter_797_; lean_object* v_rangeEndPosLine_798_; lean_object* v_rangeEndPosCharacter_799_; lean_object* v_selectionRangeStartPosLine_800_; lean_object* v_selectionRangeStartPosCharacter_801_; lean_object* v_selectionRangeEndPosLine_802_; lean_object* v_selectionRangeEndPosCharacter_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_rangeStartPosLine_796_ = lean_ctor_get(v_snd_791_, 0);
lean_inc(v_rangeStartPosLine_796_);
v_rangeStartPosCharacter_797_ = lean_ctor_get(v_snd_791_, 1);
lean_inc(v_rangeStartPosCharacter_797_);
v_rangeEndPosLine_798_ = lean_ctor_get(v_snd_791_, 2);
lean_inc(v_rangeEndPosLine_798_);
v_rangeEndPosCharacter_799_ = lean_ctor_get(v_snd_791_, 3);
lean_inc(v_rangeEndPosCharacter_799_);
v_selectionRangeStartPosLine_800_ = lean_ctor_get(v_snd_791_, 4);
lean_inc(v_selectionRangeStartPosLine_800_);
v_selectionRangeStartPosCharacter_801_ = lean_ctor_get(v_snd_791_, 5);
lean_inc(v_selectionRangeStartPosCharacter_801_);
v_selectionRangeEndPosLine_802_ = lean_ctor_get(v_snd_791_, 6);
lean_inc(v_selectionRangeEndPosLine_802_);
v_selectionRangeEndPosCharacter_803_ = lean_ctor_get(v_snd_791_, 7);
lean_inc(v_selectionRangeEndPosCharacter_803_);
lean_dec(v_snd_791_);
v___x_804_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_796_);
v___x_805_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_797_);
v___x_807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_798_);
v___x_809_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___x_810_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_799_);
v___x_811_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_800_);
v___x_813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_801_);
v___x_815_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_802_);
v___x_817_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
v___x_818_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_803_);
v___x_819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(8u);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_820_);
v___x_822_ = lean_array_push(v___x_821_, v___x_805_);
v___x_823_ = lean_array_push(v___x_822_, v___x_807_);
v___x_824_ = lean_array_push(v___x_823_, v___x_809_);
v___x_825_ = lean_array_push(v___x_824_, v___x_811_);
v___x_826_ = lean_array_push(v___x_825_, v___x_813_);
v___x_827_ = lean_array_push(v___x_826_, v___x_815_);
v___x_828_ = lean_array_push(v___x_827_, v___x_817_);
v___x_829_ = lean_array_push(v___x_828_, v___x_819_);
v___x_830_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_830_);
v___x_832_ = v___x_794_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_835_, lean_object* v_x2_836_, lean_object* v_x3_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_x1_835_);
lean_ctor_set(v___x_838_, 1, v_x2_836_);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_x3_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_840_, lean_object* v___f_841_, lean_object* v_m_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = lean_box(0);
v___x_844_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_845_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_844_, v___f_840_, v___x_843_, v_m_842_);
v___x_846_ = l_List_mapTR_loop___redArg(v___f_841_, v___x_845_, v___x_843_);
v___x_847_ = l_Lean_Json_mkObj(v___x_846_);
lean_dec(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v___x_856_, lean_object* v_m_857_, lean_object* v_k_858_, lean_object* v_v_859_){
_start:
{
if (lean_obj_tag(v_v_859_) == 4)
{
lean_object* v_elems_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_980_; 
v_elems_860_ = lean_ctor_get(v_v_859_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v_v_859_);
if (v_isSharedCheck_980_ == 0)
{
v___x_862_ = v_v_859_;
v_isShared_863_ = v_isSharedCheck_980_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_elems_860_);
lean_dec(v_v_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_980_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; uint8_t v___x_867_; 
v___x_864_ = lean_array_get_size(v_elems_860_);
v___x_865_ = lean_unsigned_to_nat(8u);
v___x_866_ = lean_nat_dec_eq(v___x_864_, v___x_865_);
v___x_867_ = lean_bool_not(v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_del_object(v___x_862_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_869_);
lean_inc(v___x_870_);
v___x_871_ = l_Lean_Json_getNat_x3f(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_871_, 1);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_881_);
lean_inc(v___x_882_);
v___x_883_ = l_Lean_Json_getNat_x3f(v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_892_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_883_, 1);
v___x_893_ = lean_unsigned_to_nat(2u);
v___x_894_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_893_);
lean_inc(v___x_894_);
v___x_895_ = l_Lean_Json_getNat_x3f(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_a_904_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_895_, 1);
v___x_905_ = lean_unsigned_to_nat(3u);
v___x_906_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_905_);
lean_inc(v___x_906_);
v___x_907_ = l_Lean_Json_getNat_x3f(v___x_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_a_904_);
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_a_916_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_907_, 1);
v___x_917_ = lean_unsigned_to_nat(4u);
v___x_918_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_917_);
lean_inc(v___x_918_);
v___x_919_ = l_Lean_Json_getNat_x3f(v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_a_916_);
lean_dec(v_a_904_);
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_928_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_919_, 1);
v___x_929_ = lean_unsigned_to_nat(5u);
v___x_930_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_929_);
lean_inc(v___x_930_);
v___x_931_ = l_Lean_Json_getNat_x3f(v___x_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_928_);
lean_dec(v_a_916_);
lean_dec(v_a_904_);
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_a_940_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_931_, 1);
v___x_941_ = lean_unsigned_to_nat(6u);
v___x_942_ = lean_array_get_borrowed(v___x_868_, v_elems_860_, v___x_941_);
lean_inc(v___x_942_);
v___x_943_ = l_Lean_Json_getNat_x3f(v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec(v_a_940_);
lean_dec(v_a_928_);
lean_dec(v_a_916_);
lean_dec(v_a_904_);
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_952_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_943_, 1);
v___x_953_ = lean_unsigned_to_nat(7u);
v___x_954_ = lean_array_get(v___x_868_, v_elems_860_, v___x_953_);
lean_dec_ref(v_elems_860_);
v___x_955_ = l_Lean_Json_getNat_x3f(v___x_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_952_);
lean_dec(v_a_940_);
lean_dec(v_a_928_);
lean_dec(v_a_916_);
lean_dec(v_a_904_);
lean_dec(v_a_892_);
lean_dec(v_a_880_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
v_a_964_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_973_ == 0)
{
v___x_966_ = v___x_955_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_955_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_968_, 0, v_a_880_);
lean_ctor_set(v___x_968_, 1, v_a_892_);
lean_ctor_set(v___x_968_, 2, v_a_904_);
lean_ctor_set(v___x_968_, 3, v_a_916_);
lean_ctor_set(v___x_968_, 4, v_a_928_);
lean_ctor_set(v___x_968_, 5, v_a_940_);
lean_ctor_set(v___x_968_, 6, v_a_952_);
lean_ctor_set(v___x_968_, 7, v_a_964_);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_856_, v_k_858_, v___x_968_, v_m_857_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
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
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v___x_974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_975_ = l_Nat_reprFast(v___x_864_);
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
lean_dec_ref(v___x_975_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 0);
lean_ctor_set(v___x_862_, 0, v___x_976_);
v___x_978_ = v___x_862_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_981_; 
lean_dec(v_v_859_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___x_985_, lean_object* v_j_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Json_getObj_x3f(v_j_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_985_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_987_, 1);
v___f_997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1));
v___x_998_ = lean_box(1);
v___x_999_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_985_, v___f_997_, v___x_998_, v_a_996_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1027_, lean_object* v_parentDecl_x3f_1028_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1028_) == 0)
{
lean_object* v_start_1029_; lean_object* v_end_1030_; lean_object* v_line_1031_; lean_object* v_character_1032_; lean_object* v_line_1033_; lean_object* v_character_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_start_1029_ = lean_ctor_get(v_range_1027_, 0);
v_end_1030_ = lean_ctor_get(v_range_1027_, 1);
v_line_1031_ = lean_ctor_get(v_start_1029_, 0);
v_character_1032_ = lean_ctor_get(v_start_1029_, 1);
v_line_1033_ = lean_ctor_get(v_end_1030_, 0);
v_character_1034_ = lean_ctor_get(v_end_1030_, 1);
v___x_1035_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1034_);
lean_inc(v_line_1033_);
lean_inc(v_character_1032_);
lean_inc(v_line_1031_);
v___x_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1036_, 0, v_line_1031_);
lean_ctor_set(v___x_1036_, 1, v_character_1032_);
lean_ctor_set(v___x_1036_, 2, v_line_1033_);
lean_ctor_set(v___x_1036_, 3, v_character_1034_);
lean_ctor_set(v___x_1036_, 4, v___x_1035_);
return v___x_1036_;
}
else
{
lean_object* v_start_1037_; lean_object* v_end_1038_; lean_object* v_line_1039_; lean_object* v_character_1040_; lean_object* v_line_1041_; lean_object* v_character_1042_; lean_object* v_val_1043_; lean_object* v___x_1044_; 
v_start_1037_ = lean_ctor_get(v_range_1027_, 0);
v_end_1038_ = lean_ctor_get(v_range_1027_, 1);
v_line_1039_ = lean_ctor_get(v_start_1037_, 0);
v_character_1040_ = lean_ctor_get(v_start_1037_, 1);
v_line_1041_ = lean_ctor_get(v_end_1038_, 0);
v_character_1042_ = lean_ctor_get(v_end_1038_, 1);
v_val_1043_ = lean_ctor_get(v_parentDecl_x3f_1028_, 0);
lean_inc(v_val_1043_);
lean_inc(v_character_1042_);
lean_inc(v_line_1041_);
lean_inc(v_character_1040_);
lean_inc(v_line_1039_);
v___x_1044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1044_, 0, v_line_1039_);
lean_ctor_set(v___x_1044_, 1, v_character_1040_);
lean_ctor_set(v___x_1044_, 2, v_line_1041_);
lean_ctor_set(v___x_1044_, 3, v_character_1042_);
lean_ctor_set(v___x_1044_, 4, v_val_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1045_, lean_object* v_parentDecl_x3f_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1045_, v_parentDecl_x3f_1046_);
lean_dec(v_parentDecl_x3f_1046_);
lean_dec_ref(v_range_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1048_){
_start:
{
lean_object* v_startPosLine_1049_; lean_object* v_startPosCharacter_1050_; lean_object* v_endPosLine_1051_; lean_object* v_endPosCharacter_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_startPosLine_1049_ = lean_ctor_get(v_l_1048_, 0);
v_startPosCharacter_1050_ = lean_ctor_get(v_l_1048_, 1);
v_endPosLine_1051_ = lean_ctor_get(v_l_1048_, 2);
v_endPosCharacter_1052_ = lean_ctor_get(v_l_1048_, 3);
lean_inc(v_startPosCharacter_1050_);
lean_inc(v_startPosLine_1049_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_startPosLine_1049_);
lean_ctor_set(v___x_1053_, 1, v_startPosCharacter_1050_);
lean_inc(v_endPosCharacter_1052_);
lean_inc(v_endPosLine_1051_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_endPosLine_1051_);
lean_ctor_set(v___x_1054_, 1, v_endPosCharacter_1052_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1056_);
lean_dec_ref(v_l_1056_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1058_){
_start:
{
lean_object* v_parentDecl_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_parentDecl_1059_ = lean_ctor_get(v_l_1058_, 4);
v___x_1060_ = lean_string_utf8_byte_size(v_parentDecl_1059_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_nat_dec_eq(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_inc_ref(v_parentDecl_1059_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_parentDecl_1059_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1065_);
lean_dec_ref(v_l_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_JsonNumber_fromNat(v_n_1067_);
v___x_1069_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1070_, lean_object* v_l_1071_){
_start:
{
lean_object* v_startPosLine_1072_; lean_object* v_startPosCharacter_1073_; lean_object* v_endPosLine_1074_; lean_object* v_endPosCharacter_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_range_1081_; lean_object* v___x_1082_; 
v_startPosLine_1072_ = lean_ctor_get(v_l_1071_, 0);
v_startPosCharacter_1073_ = lean_ctor_get(v_l_1071_, 1);
v_endPosLine_1074_ = lean_ctor_get(v_l_1071_, 2);
v_endPosCharacter_1075_ = lean_ctor_get(v_l_1071_, 3);
v___x_1076_ = lean_box(0);
lean_inc(v_endPosCharacter_1075_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_endPosCharacter_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_inc(v_endPosLine_1074_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_endPosLine_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
lean_inc(v_startPosCharacter_1073_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_startPosCharacter_1073_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
lean_inc(v_startPosLine_1072_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_startPosLine_1072_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v_range_1081_ = l_List_mapTR_loop___redArg(v___f_1070_, v___x_1080_, v___x_1076_);
v___x_1082_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1071_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = l_List_appendTR___redArg(v_range_1081_, v___x_1076_);
return v___x_1083_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v_val_1084_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v___x_1082_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_val_1084_);
lean_dec(v___x_1082_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set_tag(v___x_1086_, 3);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_val_1084_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v___x_1076_);
v___x_1091_ = l_List_appendTR___redArg(v_range_1081_, v___x_1090_);
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1094_, lean_object* v_l_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1094_, v_l_1095_);
lean_dec_ref(v_l_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_apply_1(v_locationToList_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1102_, lean_object* v___f_1103_, lean_object* v_locationToList_1104_, lean_object* v_i_1105_){
_start:
{
lean_object* v_definition_x3f_1106_; lean_object* v_usages_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1139_; 
v_definition_x3f_1106_ = lean_ctor_get(v_i_1105_, 0);
v_usages_1107_ = lean_ctor_get(v_i_1105_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_i_1105_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1109_ = v_i_1105_;
v_isShared_1110_ = v_isSharedCheck_1139_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_usages_1107_);
lean_inc(v_definition_x3f_1106_);
lean_dec(v_i_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1139_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___y_1113_; 
v___x_1111_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1106_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v_locationToList_1104_);
v___x_1129_ = lean_box(0);
v___y_1113_ = v___x_1129_;
goto v___jp_1112_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_val_1130_ = lean_ctor_get(v_definition_x3f_1106_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_definition_x3f_1106_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_definition_x3f_1106_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v_definition_x3f_1106_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_apply_1(v_locationToList_1104_, v_val_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v___y_1113_ = v___x_1136_;
goto v___jp_1112_;
}
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_inc_ref(v___x_1102_);
v___x_1114_ = l_Lean_Option_toJson___redArg(v___x_1102_, v___y_1113_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v___x_1114_);
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; size_t v_sz_1119_; size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1117_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1118_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1119_ = lean_array_size(v_usages_1107_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1118_, v___f_1103_, v_sz_1119_, v___x_1120_, v_usages_1107_);
v___x_1122_ = l_Lean_Array_toJson___redArg(v___x_1102_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1117_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1116_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_Json_mkObj(v___x_1126_);
lean_dec_ref_known(v___x_1126_, 2);
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1236_; 
v___x_1155_ = lean_array_get_size(v_a_1154_);
v___x_1156_ = lean_unsigned_to_nat(4u);
v___x_1236_ = lean_nat_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(5u);
v___x_1238_ = lean_nat_dec_eq(v___x_1155_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1240_ = l_Nat_reprFast(v___x_1155_);
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
else
{
goto v___jp_1157_;
}
}
else
{
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_array_fget_borrowed(v_a_1154_, v___x_1158_);
lean_inc(v___x_1159_);
v___x_1160_ = l_Lean_Json_getNat_x3f(v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_a_1169_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_array_fget_borrowed(v_a_1154_, v___x_1170_);
lean_inc(v___x_1171_);
v___x_1172_ = l_Lean_Json_getNat_x3f(v___x_1171_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_a_1169_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1182_ = lean_unsigned_to_nat(2u);
v___x_1183_ = lean_array_fget_borrowed(v_a_1154_, v___x_1182_);
lean_inc(v___x_1183_);
v___x_1184_ = l_Lean_Json_getNat_x3f(v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1181_);
lean_dec(v_a_1169_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1194_ = lean_unsigned_to_nat(3u);
v___x_1195_ = lean_array_fget_borrowed(v_a_1154_, v___x_1194_);
lean_inc(v___x_1195_);
v___x_1196_ = l_Lean_Json_getNat_x3f(v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1193_);
lean_dec(v_a_1181_);
lean_dec(v_a_1169_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1235_; 
v_a_1205_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1207_ = v___x_1196_;
v_isShared_1208_ = v_isSharedCheck_1235_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1196_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1235_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(5u);
v___x_1210_ = lean_nat_dec_eq(v___x_1155_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1169_);
lean_ctor_set(v___x_1212_, 1, v_a_1181_);
lean_ctor_set(v___x_1212_, 2, v_a_1193_);
lean_ctor_set(v___x_1212_, 3, v_a_1205_);
lean_ctor_set(v___x_1212_, 4, v___x_1211_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1212_);
v___x_1214_ = v___x_1207_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_del_object(v___x_1207_);
v___x_1216_ = lean_array_fget_borrowed(v_a_1154_, v___x_1156_);
lean_inc(v___x_1216_);
v___x_1217_ = l_Lean_Json_getStr_x3f(v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1205_);
lean_dec(v_a_1193_);
lean_dec(v_a_1181_);
lean_dec(v_a_1169_);
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
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
v_a_1226_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1228_ = v___x_1217_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1217_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1230_, 0, v_a_1169_);
lean_ctor_set(v___x_1230_, 1, v_a_1181_);
lean_ctor_set(v___x_1230_, 2, v_a_1193_);
lean_ctor_set(v___x_1230_, 3, v_a_1205_);
lean_ctor_set(v___x_1230_, 4, v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1243_);
lean_dec_ref(v_a_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v_toLocation_1248_, lean_object* v_j_1249_){
_start:
{
lean_object* v_definition_x3f_1251_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1249_);
v___x_1284_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1249_, v___x_1245_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_j_1249_);
lean_dec_ref(v_toLocation_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; 
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1284_, 1);
if (lean_obj_tag(v_a_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_box(0);
v_definition_x3f_1251_ = v___x_1294_;
goto v___jp_1250_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1312_; 
v_val_1295_ = lean_ctor_get(v_a_1293_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_a_1293_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1297_ = v_a_1293_;
v_isShared_1298_ = v_isSharedCheck_1312_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v_a_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1312_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; 
lean_inc_ref(v_toLocation_1248_);
v___x_1299_ = lean_apply_1(v_toLocation_1248_, v_val_1295_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_del_object(v___x_1297_);
lean_dec(v_j_1249_);
lean_dec_ref(v_toLocation_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; 
v_a_1308_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1299_, 1);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_a_1308_);
v___x_1310_ = v___x_1297_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v_definition_x3f_1251_ = v___x_1310_;
goto v___jp_1250_;
}
}
}
}
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1253_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1249_, v___x_1246_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_definition_x3f_1251_);
lean_dec_ref(v_toLocation_1248_);
lean_dec_ref(v___x_1247_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1262_; size_t v_sz_1263_; size_t v___x_1264_; lean_object* v___x_1265_; 
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1253_, 1);
v_sz_1263_ = lean_array_size(v_a_1262_);
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1247_, v_toLocation_1248_, v_sz_1263_, v___x_1264_, v_a_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_definition_x3f_1251_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1282_; 
v_a_1274_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v_definition_x3f_1251_);
lean_ctor_set(v___x_1278_, 1, v_a_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
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
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(1);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_box(1);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1329_, lean_object* v_a_1330_, lean_object* v_b_1331_, lean_object* v_c_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1330_);
lean_ctor_set(v___x_1333_, 1, v_b_1331_);
v___x_1334_ = lean_apply_2(v_f_1329_, v___x_1333_, v_c_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1335_, lean_object* v_____do__lift_1336_){
_start:
{
lean_object* v_a_1337_; lean_object* v___x_1338_; 
v_a_1337_ = lean_ctor_get(v_____do__lift_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v_____do__lift_1336_);
v___x_1338_ = lean_apply_2(v_toPure_1335_, lean_box(0), v_a_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1339_, lean_object* v_00_u03b2_1340_, lean_object* v_map_1341_, lean_object* v_init_1342_, lean_object* v_f_1343_){
_start:
{
lean_object* v_toApplicative_1344_; lean_object* v_toBind_1345_; lean_object* v_toPure_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___x_1350_; 
v_toApplicative_1344_ = lean_ctor_get(v_inst_1339_, 0);
v_toBind_1345_ = lean_ctor_get(v_inst_1339_, 1);
lean_inc(v_toBind_1345_);
v_toPure_1346_ = lean_ctor_get(v_toApplicative_1344_, 1);
lean_inc(v_toPure_1346_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1347_, 0, v_f_1343_);
v___x_1348_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1339_, v___f_1347_, v_init_1342_, v_map_1341_);
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1349_, 0, v_toPure_1346_);
v___x_1350_ = lean_apply_4(v_toBind_1345_, lean_box(0), lean_box(0), v___x_1348_, v___f_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1351_){
_start:
{
lean_object* v___f_1352_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1352_, 0, v_inst_1351_);
return v___f_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1353_, lean_object* v_inst_1354_){
_start:
{
lean_object* v___f_1355_; 
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1355_, 0, v_inst_1354_);
return v___f_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_startPosLine_1358_; lean_object* v_startPosCharacter_1359_; lean_object* v_endPosLine_1360_; lean_object* v_endPosCharacter_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_range_1367_; lean_object* v___x_1368_; 
v_startPosLine_1358_ = lean_ctor_get(v_x_1357_, 0);
v_startPosCharacter_1359_ = lean_ctor_get(v_x_1357_, 1);
v_endPosLine_1360_ = lean_ctor_get(v_x_1357_, 2);
v_endPosCharacter_1361_ = lean_ctor_get(v_x_1357_, 3);
v___x_1362_ = lean_box(0);
lean_inc(v_endPosCharacter_1361_);
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_endPosCharacter_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
lean_inc(v_endPosLine_1360_);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_endPosLine_1360_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
lean_inc(v_startPosCharacter_1359_);
v___x_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_startPosCharacter_1359_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
lean_inc(v_startPosLine_1358_);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_startPosLine_1358_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v_range_1367_ = l_List_mapTR_loop___redArg(v___f_1356_, v___x_1366_, v___x_1362_);
v___x_1368_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1357_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l_List_appendTR___redArg(v_range_1367_, v___x_1362_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
v_val_1370_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1372_ = v___x_1368_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v___x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 3);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1370_);
v___x_1375_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___x_1362_);
v___x_1377_ = l_List_appendTR___redArg(v_range_1367_, v___x_1376_);
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1380_, v_x_1381_);
lean_dec_ref(v_x_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1383_, lean_object* v___f_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_snd_1386_; lean_object* v_fst_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1448_; 
v_snd_1386_ = lean_ctor_get(v_x_1385_, 1);
v_fst_1387_ = lean_ctor_get(v_x_1385_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1389_ = v_x_1385_;
v_isShared_1390_ = v_isSharedCheck_1448_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snd_1386_);
lean_inc(v_fst_1387_);
lean_dec(v_x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1448_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_definition_x3f_1391_; lean_object* v_usages_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1447_; 
v_definition_x3f_1391_ = lean_ctor_get(v_snd_1386_, 0);
v_usages_1392_ = lean_ctor_get(v_snd_1386_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_snd_1386_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1394_ = v_snd_1386_;
v_isShared_1395_ = v_isSharedCheck_1447_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_usages_1392_);
lean_inc(v_definition_x3f_1391_);
lean_dec(v_snd_1386_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1447_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___y_1401_; lean_object* v___y_1421_; 
v___x_1396_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1387_);
v___x_1397_ = l_Lean_Json_compress(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1399_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1391_) == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v___f_1384_);
v___x_1423_ = lean_box(0);
v___y_1401_ = v___x_1423_;
goto v___jp_1400_;
}
else
{
lean_object* v_val_1424_; lean_object* v_startPosLine_1425_; lean_object* v_startPosCharacter_1426_; lean_object* v_endPosLine_1427_; lean_object* v_endPosCharacter_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_range_1434_; lean_object* v___x_1435_; 
v_val_1424_ = lean_ctor_get(v_definition_x3f_1391_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v_definition_x3f_1391_, 1);
v_startPosLine_1425_ = lean_ctor_get(v_val_1424_, 0);
v_startPosCharacter_1426_ = lean_ctor_get(v_val_1424_, 1);
v_endPosLine_1427_ = lean_ctor_get(v_val_1424_, 2);
v_endPosCharacter_1428_ = lean_ctor_get(v_val_1424_, 3);
v___x_1429_ = lean_box(0);
lean_inc(v_endPosCharacter_1428_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_endPosCharacter_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc(v_endPosLine_1427_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_endPosLine_1427_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_inc(v_startPosCharacter_1426_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_startPosCharacter_1426_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_inc(v_startPosLine_1425_);
v___x_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_startPosLine_1425_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v_range_1434_ = l_List_mapTR_loop___redArg(v___f_1384_, v___x_1433_, v___x_1429_);
v___x_1435_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1424_);
lean_dec(v_val_1424_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = l_List_appendTR___redArg(v_range_1434_, v___x_1429_);
v___y_1421_ = v___x_1436_;
goto v___jp_1420_;
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v___x_1435_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_val_1437_);
lean_dec(v___x_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 3);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_val_1437_);
v___x_1442_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___x_1429_);
v___x_1444_ = l_List_appendTR___redArg(v_range_1434_, v___x_1443_);
v___y_1421_ = v___x_1444_;
goto v___jp_1420_;
}
}
}
}
v___jp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = l_Lean_Option_toJson___redArg(v___x_1398_, v___y_1401_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___x_1402_);
lean_ctor_set(v___x_1389_, 0, v___x_1399_);
v___x_1404_ = v___x_1389_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1405_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1406_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1407_ = lean_array_size(v_usages_1392_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___f_1383_, v_sz_1407_, v___x_1408_, v_usages_1392_);
v___x_1410_ = l_Lean_Array_toJson___redArg(v___x_1398_, v___x_1409_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___x_1410_);
lean_ctor_set(v___x_1394_, 0, v___x_1405_);
v___x_1412_ = v___x_1394_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1404_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_Json_mkObj(v___x_1415_);
lean_dec_ref_known(v___x_1415_, 2);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1397_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
return v___x_1417_;
}
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1421_);
v___y_1401_ = v___x_1422_;
goto v___jp_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1449_, lean_object* v_x2_1450_, lean_object* v_x3_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_x1_1449_);
lean_ctor_set(v___x_1452_, 1, v_x2_1450_);
v___x_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_x3_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1454_, lean_object* v___f_1455_, lean_object* v_m_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1459_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1458_, v___f_1454_, v___x_1457_, v_m_1456_);
v___x_1460_ = l_List_mapTR_loop___redArg(v___f_1455_, v___x_1459_, v___x_1457_);
v___x_1461_ = l_Lean_Json_mkObj(v___x_1460_);
lean_dec(v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1472_, lean_object* v_m_1473_, lean_object* v_k_1474_, lean_object* v_v_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Json_parse(v_k_1474_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1486_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1498_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1475_);
v___x_1499_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1475_, v___x_1497_, v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1629_; 
v_a_1508_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1510_ = v___x_1499_;
v_isShared_1511_ = v_isSharedCheck_1629_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1499_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1629_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v_definition_x3f_1514_; lean_object* v_a_1549_; 
v___x_1512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v___x_1551_; 
lean_del_object(v___x_1510_);
v___x_1551_ = lean_box(0);
v_definition_x3f_1514_ = v___x_1551_;
goto v___jp_1513_;
}
else
{
lean_object* v_val_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1620_; 
v_val_1552_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v_a_1508_, 1);
v___x_1553_ = lean_array_get_size(v_val_1552_);
v___x_1554_ = lean_unsigned_to_nat(4u);
v___x_1620_ = lean_nat_dec_eq(v___x_1553_, v___x_1554_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(5u);
v___x_1622_ = lean_nat_dec_eq(v___x_1553_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec(v_val_1552_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v___x_1623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1624_ = l_Nat_reprFast(v___x_1553_);
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
lean_dec_ref(v___x_1624_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1625_);
v___x_1627_ = v___x_1510_;
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
else
{
lean_del_object(v___x_1510_);
goto v___jp_1555_;
}
}
else
{
lean_del_object(v___x_1510_);
goto v___jp_1555_;
}
v___jp_1555_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_array_fget_borrowed(v_val_1552_, v___x_1556_);
lean_inc(v___x_1557_);
v___x_1558_ = l_Lean_Json_getNat_x3f(v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_val_1552_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
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
lean_dec_ref_known(v___x_1558_, 1);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_array_fget_borrowed(v_val_1552_, v___x_1568_);
lean_inc(v___x_1569_);
v___x_1570_ = l_Lean_Json_getNat_x3f(v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1567_);
lean_dec(v_val_1552_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
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
lean_dec_ref_known(v___x_1570_, 1);
v___x_1580_ = lean_unsigned_to_nat(2u);
v___x_1581_ = lean_array_fget_borrowed(v_val_1552_, v___x_1580_);
lean_inc(v___x_1581_);
v___x_1582_ = l_Lean_Json_getNat_x3f(v___x_1581_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1579_);
lean_dec(v_a_1567_);
lean_dec(v_val_1552_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
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
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_a_1591_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1592_ = lean_unsigned_to_nat(3u);
v___x_1593_ = lean_array_fget_borrowed(v_val_1552_, v___x_1592_);
lean_inc(v___x_1593_);
v___x_1594_ = l_Lean_Json_getNat_x3f(v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1591_);
lean_dec(v_a_1579_);
lean_dec(v_a_1567_);
lean_dec(v_val_1552_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1604_ = lean_unsigned_to_nat(5u);
v___x_1605_ = lean_nat_dec_eq(v___x_1553_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_val_1552_);
v___x_1606_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1607_, 0, v_a_1567_);
lean_ctor_set(v___x_1607_, 1, v_a_1579_);
lean_ctor_set(v___x_1607_, 2, v_a_1591_);
lean_ctor_set(v___x_1607_, 3, v_a_1603_);
lean_ctor_set(v___x_1607_, 4, v___x_1606_);
v_a_1549_ = v___x_1607_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_array_fget(v_val_1552_, v___x_1554_);
lean_dec(v_val_1552_);
v___x_1609_ = l_Lean_Json_getStr_x3f(v___x_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1603_);
lean_dec(v_a_1591_);
lean_dec(v_a_1579_);
lean_dec(v_a_1567_);
lean_dec(v_a_1495_);
lean_dec(v_v_1475_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1619_, 0, v_a_1567_);
lean_ctor_set(v___x_1619_, 1, v_a_1579_);
lean_ctor_set(v___x_1619_, 2, v_a_1591_);
lean_ctor_set(v___x_1619_, 3, v_a_1603_);
lean_ctor_set(v___x_1619_, 4, v_a_1618_);
v_a_1549_ = v___x_1619_;
goto v___jp_1548_;
}
}
}
}
}
}
}
}
v___jp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1516_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1475_, v___x_1512_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_definition_x3f_1514_);
lean_dec(v_a_1495_);
lean_dec(v_m_1473_);
lean_dec_ref(v_toLocation_1472_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1525_; size_t v_sz_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1516_, 1);
v_sz_1526_ = lean_array_size(v_a_1525_);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1496_, v_toLocation_1472_, v_sz_1526_, v___x_1527_, v_a_1525_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_definition_x3f_1514_);
lean_dec(v_a_1495_);
lean_dec(v_m_1473_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1547_; 
v_a_1537_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1539_ = v___x_1528_;
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_definition_x3f_1514_);
lean_ctor_set(v___x_1541_, 1, v_a_1537_);
v___x_1542_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1542_, v_a_1495_, v___x_1541_, v_m_1473_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1543_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
v___jp_1548_:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v_a_1549_);
v_definition_x3f_1514_ = v___x_1550_;
goto v___jp_1513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1630_, lean_object* v___f_1631_, lean_object* v_j_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Json_getObj_x3f(v_j_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec_ref(v___f_1631_);
lean_dec_ref(v___x_1630_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1642_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1643_ = lean_box(1);
v___x_1644_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1630_, v___f_1631_, v___x_1643_, v_a_1642_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1651_, lean_object* v_k_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = l_Lean_Json_getObjValD(v_j_1651_, v_k_1652_);
v___x_1654_ = l_Lean_Json_getNat_x3f(v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1655_, lean_object* v_k_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1655_, v_k_1656_);
lean_dec_ref(v_k_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = l_Lean_Json_getObjValD(v_j_1658_, v_k_1659_);
v___x_1661_ = l_Lean_Json_getBool_x3f(v___x_1660_);
lean_dec(v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1662_, lean_object* v_k_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1662_, v_k_1663_);
lean_dec_ref(v_k_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1667_, size_t v_i_1668_, lean_object* v_bs_1669_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_usize_dec_lt(v_i_1668_, v_sz_1667_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_bs_1669_);
return v___x_1673_;
}
else
{
lean_object* v_v_1674_; 
v_v_1674_ = lean_array_uget_borrowed(v_bs_1669_, v_i_1668_);
if (lean_obj_tag(v_v_1674_) == 4)
{
lean_object* v_elems_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_elems_1675_ = lean_ctor_get(v_v_1674_, 0);
v___x_1676_ = lean_array_get_size(v_elems_1675_);
v___x_1677_ = lean_unsigned_to_nat(4u);
v___x_1678_ = lean_nat_dec_eq(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_dec_ref(v_bs_1669_);
goto v___jp_1670_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_array_fget_borrowed(v_elems_1675_, v___x_1679_);
lean_inc(v___x_1680_);
v___x_1681_ = l_Lean_Json_getStr_x3f(v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_bs_1669_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_array_fget_borrowed(v_elems_1675_, v___x_1691_);
v___x_1693_ = l_Lean_Json_getBool_x3f(v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1690_);
lean_dec_ref(v_bs_1669_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1703_ = lean_unsigned_to_nat(2u);
v___x_1704_ = lean_array_fget_borrowed(v_elems_1675_, v___x_1703_);
v___x_1705_ = l_Lean_Json_getBool_x3f(v___x_1704_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_a_1702_);
lean_dec(v_a_1690_);
lean_dec_ref(v_bs_1669_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1714_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1715_ = lean_unsigned_to_nat(3u);
v___x_1716_ = lean_array_fget_borrowed(v_elems_1675_, v___x_1715_);
v___x_1717_ = l_Lean_Json_getBool_x3f(v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1714_);
lean_dec(v_a_1702_);
lean_dec(v_a_1690_);
lean_dec_ref(v_bs_1669_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v_bs_x27_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; uint8_t v___x_1730_; uint8_t v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v_a_1726_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1717_, 1);
v_bs_x27_1727_ = lean_array_uset(v_bs_1669_, v_i_1668_, v___x_1679_);
v___x_1728_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1728_, 0, v_a_1690_);
v___x_1729_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
lean_ctor_set_uint8(v___x_1728_, sizeof(void*)*1, v___x_1729_);
v___x_1730_ = lean_unbox(v_a_1714_);
lean_dec(v_a_1714_);
lean_ctor_set_uint8(v___x_1728_, sizeof(void*)*1 + 1, v___x_1730_);
v___x_1731_ = lean_unbox(v_a_1726_);
lean_dec(v_a_1726_);
lean_ctor_set_uint8(v___x_1728_, sizeof(void*)*1 + 2, v___x_1731_);
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_add(v_i_1668_, v___x_1732_);
v___x_1734_ = lean_array_uset(v_bs_x27_1727_, v_i_1668_, v___x_1728_);
v_i_1668_ = v___x_1733_;
v_bs_1669_ = v___x_1734_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1669_);
goto v___jp_1670_;
}
}
v___jp_1670_:
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1736_, lean_object* v_i_1737_, lean_object* v_bs_1738_){
_start:
{
size_t v_sz_boxed_1739_; size_t v_i_boxed_1740_; lean_object* v_res_1741_; 
v_sz_boxed_1739_ = lean_unbox_usize(v_sz_1736_);
lean_dec(v_sz_1736_);
v_i_boxed_1740_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1739_, v_i_boxed_1740_, v_bs_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1744_) == 4)
{
lean_object* v_elems_1745_; size_t v_sz_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v_elems_1745_ = lean_ctor_get(v_x_1744_, 0);
lean_inc_ref(v_elems_1745_);
lean_dec_ref_known(v_x_1744_, 1);
v_sz_1746_ = lean_array_size(v_elems_1745_);
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1746_, v___x_1747_, v_elems_1745_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1749_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1750_ = lean_unsigned_to_nat(80u);
v___x_1751_ = l_Lean_Json_pretty(v_x_1744_, v___x_1750_);
v___x_1752_ = lean_string_append(v___x_1749_, v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1754_ = lean_string_append(v___x_1752_, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1756_, lean_object* v_k_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = l_Lean_Json_getObjValD(v_j_1756_, v_k_1757_);
v___x_1759_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1760_, lean_object* v_k_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1760_, v_k_1761_);
lean_dec_ref(v_k_1761_);
return v_res_1762_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = 1;
v___x_1772_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1777_ = lean_string_append(v___x_1776_, v___x_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = 1;
v___x_1781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1781_, v___x_1780_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1784_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1785_ = lean_string_append(v___x_1784_, v___x_1783_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1788_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1789_ = lean_string_append(v___x_1788_, v___x_1787_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = 1;
v___x_1794_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1795_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1797_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1798_ = lean_string_append(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1800_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1801_ = lean_string_append(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = 1;
v___x_1806_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1806_, v___x_1805_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1809_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1810_ = lean_string_append(v___x_1809_, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1812_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1813_ = lean_string_append(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1814_);
v___x_1816_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1814_, v___x_1815_);
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
v___x_1821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
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
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_json_1814_);
v_a_1827_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1816_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1816_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 0);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1835_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1814_);
v___x_1837_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1814_, v___x_1836_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1835_);
lean_dec(v_json_1814_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1847_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1847_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1843_ = lean_string_append(v___x_1842_, v_a_1838_);
lean_dec(v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1843_);
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1835_);
lean_dec(v_json_1814_);
v_a_1848_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1837_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1837_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 0);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_a_1856_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1857_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1858_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1814_, v___x_1857_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_a_1856_);
lean_dec(v_a_1835_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1864_ = lean_string_append(v___x_1863_, v_a_1859_);
lean_dec(v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1856_);
lean_dec(v_a_1835_);
v_a_1869_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1858_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1858_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1886_; 
v_a_1877_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1879_ = v___x_1858_;
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1858_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1881_, 0, v_a_1835_);
lean_ctor_set(v___x_1881_, 1, v_a_1877_);
v___x_1882_ = lean_unbox(v_a_1856_);
lean_dec(v_a_1856_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*2, v___x_1882_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1889_, size_t v_i_1890_, lean_object* v_bs_1891_){
_start:
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_usize_dec_lt(v_i_1890_, v_sz_1889_);
if (v___x_1892_ == 0)
{
return v_bs_1891_;
}
else
{
lean_object* v_v_1893_; lean_object* v_module_1894_; uint8_t v_isPrivate_1895_; uint8_t v_isAll_1896_; uint8_t v_isMeta_1897_; lean_object* v___x_1898_; lean_object* v_bs_x27_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v_v_1893_ = lean_array_uget_borrowed(v_bs_1891_, v_i_1890_);
v_module_1894_ = lean_ctor_get(v_v_1893_, 0);
lean_inc_ref(v_module_1894_);
v_isPrivate_1895_ = lean_ctor_get_uint8(v_v_1893_, sizeof(void*)*1);
v_isAll_1896_ = lean_ctor_get_uint8(v_v_1893_, sizeof(void*)*1 + 1);
v_isMeta_1897_ = lean_ctor_get_uint8(v_v_1893_, sizeof(void*)*1 + 2);
v___x_1898_ = lean_unsigned_to_nat(0u);
v_bs_x27_1899_ = lean_array_uset(v_bs_1891_, v_i_1890_, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_module_1894_);
v___x_1901_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1901_, 0, v_isPrivate_1895_);
v___x_1902_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1902_, 0, v_isAll_1896_);
v___x_1903_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1903_, 0, v_isMeta_1897_);
v___x_1904_ = lean_unsigned_to_nat(4u);
v___x_1905_ = lean_mk_empty_array_with_capacity(v___x_1904_);
v___x_1906_ = lean_array_push(v___x_1905_, v___x_1900_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1901_);
v___x_1908_ = lean_array_push(v___x_1907_, v___x_1902_);
v___x_1909_ = lean_array_push(v___x_1908_, v___x_1903_);
v___x_1910_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_add(v_i_1890_, v___x_1911_);
v___x_1913_ = lean_array_uset(v_bs_x27_1899_, v_i_1890_, v___x_1910_);
v_i_1890_ = v___x_1912_;
v_bs_1891_ = v___x_1913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1915_, lean_object* v_i_1916_, lean_object* v_bs_1917_){
_start:
{
size_t v_sz_boxed_1918_; size_t v_i_boxed_1919_; lean_object* v_res_1920_; 
v_sz_boxed_1918_ = lean_unbox_usize(v_sz_1915_);
lean_dec(v_sz_1915_);
v_i_boxed_1919_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1918_, v_i_boxed_1919_, v_bs_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1921_){
_start:
{
size_t v_sz_1922_; size_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_sz_1922_ = lean_array_size(v_a_1921_);
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1922_, v___x_1923_, v_a_1921_);
v___x_1925_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
if (lean_obj_tag(v_a_1926_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_array_to_list(v_a_1927_);
return v___x_1928_;
}
else
{
lean_object* v_head_1929_; lean_object* v_tail_1930_; lean_object* v___x_1931_; 
v_head_1929_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_head_1929_);
v_tail_1930_ = lean_ctor_get(v_a_1926_, 1);
lean_inc(v_tail_1930_);
lean_dec_ref_known(v_a_1926_, 2);
v___x_1931_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1927_, v_head_1929_);
v_a_1926_ = v_tail_1930_;
v_a_1927_ = v___x_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1935_){
_start:
{
lean_object* v_version_1936_; uint8_t v_isSetupFailure_1937_; lean_object* v_directImports_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_version_1936_ = lean_ctor_get(v_x_1935_, 0);
lean_inc(v_version_1936_);
v_isSetupFailure_1937_ = lean_ctor_get_uint8(v_x_1935_, sizeof(void*)*2);
v_directImports_1938_ = lean_ctor_get(v_x_1935_, 1);
lean_inc_ref(v_directImports_1938_);
lean_dec_ref(v_x_1935_);
v___x_1939_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1940_ = l_Lean_JsonNumber_fromNat(v_version_1936_);
v___x_1941_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1939_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1946_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1946_, 0, v_isSetupFailure_1937_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1943_);
v___x_1949_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1950_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1938_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1943_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v___x_1943_);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1948_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1944_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1957_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1955_, v___x_1956_);
v___x_1958_ = l_Lean_Json_mkObj(v___x_1957_);
lean_dec(v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1961_, lean_object* v_v_1962_, lean_object* v_t_1963_){
_start:
{
if (lean_obj_tag(v_t_1963_) == 0)
{
lean_object* v_size_1964_; lean_object* v_k_1965_; lean_object* v_v_1966_; lean_object* v_l_1967_; lean_object* v_r_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2248_; 
v_size_1964_ = lean_ctor_get(v_t_1963_, 0);
v_k_1965_ = lean_ctor_get(v_t_1963_, 1);
v_v_1966_ = lean_ctor_get(v_t_1963_, 2);
v_l_1967_ = lean_ctor_get(v_t_1963_, 3);
v_r_1968_ = lean_ctor_get(v_t_1963_, 4);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_t_1963_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_1970_ = v_t_1963_;
v_isShared_1971_ = v_isSharedCheck_2248_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_r_1968_);
lean_inc(v_l_1967_);
lean_inc(v_v_1966_);
lean_inc(v_k_1965_);
lean_inc(v_size_1964_);
lean_dec(v_t_1963_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2248_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_string_compare(v_k_1961_, v_k_1965_);
switch(v___x_1972_)
{
case 0:
{
lean_object* v_impl_1973_; lean_object* v___x_1974_; 
lean_dec(v_size_1964_);
v_impl_1973_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1961_, v_v_1962_, v_l_1967_);
v___x_1974_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1968_) == 0)
{
lean_object* v_size_1975_; lean_object* v_size_1976_; lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v_l_1979_; lean_object* v_r_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v_size_1975_ = lean_ctor_get(v_r_1968_, 0);
v_size_1976_ = lean_ctor_get(v_impl_1973_, 0);
lean_inc(v_size_1976_);
v_k_1977_ = lean_ctor_get(v_impl_1973_, 1);
lean_inc(v_k_1977_);
v_v_1978_ = lean_ctor_get(v_impl_1973_, 2);
lean_inc(v_v_1978_);
v_l_1979_ = lean_ctor_get(v_impl_1973_, 3);
lean_inc(v_l_1979_);
v_r_1980_ = lean_ctor_get(v_impl_1973_, 4);
lean_inc(v_r_1980_);
v___x_1981_ = lean_unsigned_to_nat(3u);
v___x_1982_ = lean_nat_mul(v___x_1981_, v_size_1975_);
v___x_1983_ = lean_nat_dec_lt(v___x_1982_, v_size_1976_);
lean_dec(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_dec(v_r_1980_);
lean_dec(v_l_1979_);
lean_dec(v_v_1978_);
lean_dec(v_k_1977_);
v___x_1984_ = lean_nat_add(v___x_1974_, v_size_1976_);
lean_dec(v_size_1976_);
v___x_1985_ = lean_nat_add(v___x_1984_, v_size_1975_);
lean_dec(v___x_1984_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 3, v_impl_1973_);
lean_ctor_set(v___x_1970_, 0, v___x_1985_);
v___x_1987_ = v___x_1970_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_impl_1973_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_r_1968_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2054_; 
v_isSharedCheck_2054_ = !lean_is_exclusive(v_impl_1973_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2055_ = lean_ctor_get(v_impl_1973_, 4);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_impl_1973_, 3);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_impl_1973_, 2);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_impl_1973_, 1);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_impl_1973_, 0);
lean_dec(v_unused_2059_);
v___x_1990_ = v_impl_1973_;
v_isShared_1991_ = v_isSharedCheck_2054_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v_impl_1973_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2054_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_size_1992_; lean_object* v_size_1993_; lean_object* v_k_1994_; lean_object* v_v_1995_; lean_object* v_l_1996_; lean_object* v_r_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_size_1992_ = lean_ctor_get(v_l_1979_, 0);
v_size_1993_ = lean_ctor_get(v_r_1980_, 0);
v_k_1994_ = lean_ctor_get(v_r_1980_, 1);
v_v_1995_ = lean_ctor_get(v_r_1980_, 2);
v_l_1996_ = lean_ctor_get(v_r_1980_, 3);
v_r_1997_ = lean_ctor_get(v_r_1980_, 4);
v___x_1998_ = lean_unsigned_to_nat(2u);
v___x_1999_ = lean_nat_mul(v___x_1998_, v_size_1992_);
v___x_2000_ = lean_nat_dec_lt(v_size_1993_, v___x_1999_);
lean_dec(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2029_; 
lean_inc(v_r_1997_);
lean_inc(v_l_1996_);
lean_inc(v_v_1995_);
lean_inc(v_k_1994_);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_r_1980_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2030_ = lean_ctor_get(v_r_1980_, 4);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1980_, 3);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1980_, 2);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_1980_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_r_1980_, 0);
lean_dec(v_unused_2034_);
v___x_2002_ = v_r_1980_;
v_isShared_2003_ = v_isSharedCheck_2029_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v_r_1980_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2029_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___x_2017_; lean_object* v___y_2019_; 
v___x_2004_ = lean_nat_add(v___x_1974_, v_size_1976_);
lean_dec(v_size_1976_);
v___x_2005_ = lean_nat_add(v___x_2004_, v_size_1975_);
lean_dec(v___x_2004_);
v___x_2017_ = lean_nat_add(v___x_1974_, v_size_1992_);
if (lean_obj_tag(v_l_1996_) == 0)
{
lean_object* v_size_2027_; 
v_size_2027_ = lean_ctor_get(v_l_1996_, 0);
lean_inc(v_size_2027_);
v___y_2019_ = v_size_2027_;
goto v___jp_2018_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___y_2019_ = v___x_2028_;
goto v___jp_2018_;
}
v___jp_2006_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_nat_add(v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v_r_1968_);
lean_ctor_set(v___x_2002_, 3, v_r_1997_);
lean_ctor_set(v___x_2002_, 2, v_v_1966_);
lean_ctor_set(v___x_2002_, 1, v_k_1965_);
lean_ctor_set(v___x_2002_, 0, v___x_2010_);
v___x_2012_ = v___x_2002_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_r_1997_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_r_1968_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 4, v___x_2012_);
lean_ctor_set(v___x_1990_, 3, v___y_2007_);
lean_ctor_set(v___x_1990_, 2, v_v_1995_);
lean_ctor_set(v___x_1990_, 1, v_k_1994_);
lean_ctor_set(v___x_1990_, 0, v___x_2005_);
v___x_2014_ = v___x_1990_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1994_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1995_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v___y_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
v___jp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_nat_add(v___x_2017_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec(v___x_2017_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_l_1996_);
lean_ctor_set(v___x_1970_, 3, v_l_1979_);
lean_ctor_set(v___x_1970_, 2, v_v_1978_);
lean_ctor_set(v___x_1970_, 1, v_k_1977_);
lean_ctor_set(v___x_1970_, 0, v___x_2020_);
v___x_2022_ = v___x_1970_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v_l_1996_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_nat_add(v___x_1974_, v_size_1975_);
if (lean_obj_tag(v_r_1997_) == 0)
{
lean_object* v_size_2024_; 
v_size_2024_ = lean_ctor_get(v_r_1997_, 0);
lean_inc(v_size_2024_);
v___y_2007_ = v___x_2022_;
v___y_2008_ = v___x_2023_;
v___y_2009_ = v_size_2024_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___y_2007_ = v___x_2022_;
v___y_2008_ = v___x_2023_;
v___y_2009_ = v___x_2025_;
goto v___jp_2006_;
}
}
}
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_del_object(v___x_1970_);
v___x_2035_ = lean_nat_add(v___x_1974_, v_size_1976_);
lean_dec(v_size_1976_);
v___x_2036_ = lean_nat_add(v___x_2035_, v_size_1975_);
lean_dec(v___x_2035_);
v___x_2037_ = lean_nat_add(v___x_1974_, v_size_1975_);
v___x_2038_ = lean_nat_add(v___x_2037_, v_size_1993_);
lean_dec(v___x_2037_);
lean_inc_ref(v_r_1968_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 4, v_r_1968_);
lean_ctor_set(v___x_1990_, 3, v_r_1980_);
lean_ctor_set(v___x_1990_, 2, v_v_1966_);
lean_ctor_set(v___x_1990_, 1, v_k_1965_);
lean_ctor_set(v___x_1990_, 0, v___x_2038_);
v___x_2040_ = v___x_1990_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_r_1980_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_r_1968_);
v___x_2040_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_isSharedCheck_2047_ = !lean_is_exclusive(v_r_1968_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2048_ = lean_ctor_get(v_r_1968_, 4);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_r_1968_, 3);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_r_1968_, 2);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_r_1968_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_r_1968_, 0);
lean_dec(v_unused_2052_);
v___x_2042_ = v_r_1968_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v_r_1968_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 4, v___x_2040_);
lean_ctor_set(v___x_2042_, 3, v_l_1979_);
lean_ctor_set(v___x_2042_, 2, v_v_1978_);
lean_ctor_set(v___x_2042_, 1, v_k_1977_);
lean_ctor_set(v___x_2042_, 0, v___x_2036_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_l_1979_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v___x_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2060_; 
v_l_2060_ = lean_ctor_get(v_impl_1973_, 3);
lean_inc(v_l_2060_);
if (lean_obj_tag(v_l_2060_) == 0)
{
lean_object* v_r_2061_; lean_object* v_k_2062_; lean_object* v_v_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_r_2061_ = lean_ctor_get(v_impl_1973_, 4);
v_k_2062_ = lean_ctor_get(v_impl_1973_, 1);
v_v_2063_ = lean_ctor_get(v_impl_1973_, 2);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_impl_1973_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; 
v_unused_2075_ = lean_ctor_get(v_impl_1973_, 3);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_impl_1973_, 0);
lean_dec(v_unused_2076_);
v___x_2065_ = v_impl_1973_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_r_2061_);
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
lean_dec(v_impl_1973_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2061_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 3, v_r_2061_);
lean_ctor_set(v___x_2065_, 2, v_v_1966_);
lean_ctor_set(v___x_2065_, 1, v_k_1965_);
lean_ctor_set(v___x_2065_, 0, v___x_1974_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_r_2061_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_r_2061_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_2069_);
lean_ctor_set(v___x_1970_, 3, v_l_2060_);
lean_ctor_set(v___x_1970_, 2, v_v_2063_);
lean_ctor_set(v___x_1970_, 1, v_k_2062_);
lean_ctor_set(v___x_1970_, 0, v___x_2067_);
v___x_2071_ = v___x_1970_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_l_2060_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v___x_2069_);
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
lean_object* v_r_2077_; 
v_r_2077_ = lean_ctor_get(v_impl_1973_, 4);
lean_inc(v_r_2077_);
if (lean_obj_tag(v_r_2077_) == 0)
{
lean_object* v_k_2078_; lean_object* v_v_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2102_; 
v_k_2078_ = lean_ctor_get(v_impl_1973_, 1);
v_v_2079_ = lean_ctor_get(v_impl_1973_, 2);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_impl_1973_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; lean_object* v_unused_2104_; lean_object* v_unused_2105_; 
v_unused_2103_ = lean_ctor_get(v_impl_1973_, 4);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_impl_1973_, 3);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_impl_1973_, 0);
lean_dec(v_unused_2105_);
v___x_2081_ = v_impl_1973_;
v_isShared_2082_ = v_isSharedCheck_2102_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_v_2079_);
lean_inc(v_k_2078_);
lean_dec(v_impl_1973_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2102_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_k_2083_; lean_object* v_v_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_k_2083_ = lean_ctor_get(v_r_2077_, 1);
v_v_2084_ = lean_ctor_get(v_r_2077_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_r_2077_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; lean_object* v_unused_2100_; lean_object* v_unused_2101_; 
v_unused_2099_ = lean_ctor_get(v_r_2077_, 4);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_r_2077_, 3);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_r_2077_, 0);
lean_dec(v_unused_2101_);
v___x_2086_ = v_r_2077_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_v_2084_);
lean_inc(v_k_2083_);
lean_dec(v_r_2077_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_unsigned_to_nat(3u);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 4, v_l_2060_);
lean_ctor_set(v___x_2086_, 3, v_l_2060_);
lean_ctor_set(v___x_2086_, 2, v_v_2079_);
lean_ctor_set(v___x_2086_, 1, v_k_2078_);
lean_ctor_set(v___x_2086_, 0, v___x_1974_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_l_2060_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_l_2060_);
v___x_2090_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v_l_2060_);
lean_ctor_set(v___x_2081_, 2, v_v_1966_);
lean_ctor_set(v___x_2081_, 1, v_k_1965_);
lean_ctor_set(v___x_2081_, 0, v___x_1974_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_l_2060_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_l_2060_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_2092_);
lean_ctor_set(v___x_1970_, 3, v___x_2090_);
lean_ctor_set(v___x_1970_, 2, v_v_2084_);
lean_ctor_set(v___x_1970_, 1, v_k_2083_);
lean_ctor_set(v___x_1970_, 0, v___x_2088_);
v___x_2094_ = v___x_1970_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_k_2083_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_v_2084_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_unsigned_to_nat(2u);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_r_2077_);
lean_ctor_set(v___x_1970_, 3, v_impl_1973_);
lean_ctor_set(v___x_1970_, 0, v___x_2106_);
v___x_2108_ = v___x_1970_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_impl_1973_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_r_2077_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2111_; 
lean_dec(v_v_1966_);
lean_dec(v_k_1965_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 2, v_v_1962_);
lean_ctor_set(v___x_1970_, 1, v_k_1961_);
v___x_2111_ = v___x_1970_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_size_1964_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_r_1968_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
default: 
{
lean_object* v_impl_2113_; lean_object* v___x_2114_; 
lean_dec(v_size_1964_);
v_impl_2113_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1961_, v_v_1962_, v_r_1968_);
v___x_2114_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1967_) == 0)
{
lean_object* v_size_2115_; lean_object* v_size_2116_; lean_object* v_k_2117_; lean_object* v_v_2118_; lean_object* v_l_2119_; lean_object* v_r_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v_size_2115_ = lean_ctor_get(v_l_1967_, 0);
v_size_2116_ = lean_ctor_get(v_impl_2113_, 0);
lean_inc(v_size_2116_);
v_k_2117_ = lean_ctor_get(v_impl_2113_, 1);
lean_inc(v_k_2117_);
v_v_2118_ = lean_ctor_get(v_impl_2113_, 2);
lean_inc(v_v_2118_);
v_l_2119_ = lean_ctor_get(v_impl_2113_, 3);
lean_inc(v_l_2119_);
v_r_2120_ = lean_ctor_get(v_impl_2113_, 4);
lean_inc(v_r_2120_);
v___x_2121_ = lean_unsigned_to_nat(3u);
v___x_2122_ = lean_nat_mul(v___x_2121_, v_size_2115_);
v___x_2123_ = lean_nat_dec_lt(v___x_2122_, v_size_2116_);
lean_dec(v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_r_2120_);
lean_dec(v_l_2119_);
lean_dec(v_v_2118_);
lean_dec(v_k_2117_);
v___x_2124_ = lean_nat_add(v___x_2114_, v_size_2115_);
v___x_2125_ = lean_nat_add(v___x_2124_, v_size_2116_);
lean_dec(v_size_2116_);
lean_dec(v___x_2124_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_impl_2113_);
lean_ctor_set(v___x_1970_, 0, v___x_2125_);
v___x_2127_ = v___x_1970_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_impl_2113_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2192_; 
v_isSharedCheck_2192_ = !lean_is_exclusive(v_impl_2113_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; 
v_unused_2193_ = lean_ctor_get(v_impl_2113_, 4);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_impl_2113_, 3);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_impl_2113_, 2);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_impl_2113_, 1);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_impl_2113_, 0);
lean_dec(v_unused_2197_);
v___x_2130_ = v_impl_2113_;
v_isShared_2131_ = v_isSharedCheck_2192_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v_impl_2113_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2192_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_size_2132_; lean_object* v_k_2133_; lean_object* v_v_2134_; lean_object* v_l_2135_; lean_object* v_r_2136_; lean_object* v_size_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_size_2132_ = lean_ctor_get(v_l_2119_, 0);
v_k_2133_ = lean_ctor_get(v_l_2119_, 1);
v_v_2134_ = lean_ctor_get(v_l_2119_, 2);
v_l_2135_ = lean_ctor_get(v_l_2119_, 3);
v_r_2136_ = lean_ctor_get(v_l_2119_, 4);
v_size_2137_ = lean_ctor_get(v_r_2120_, 0);
v___x_2138_ = lean_unsigned_to_nat(2u);
v___x_2139_ = lean_nat_mul(v___x_2138_, v_size_2137_);
v___x_2140_ = lean_nat_dec_lt(v_size_2132_, v___x_2139_);
lean_dec(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2168_; 
lean_inc(v_r_2136_);
lean_inc(v_l_2135_);
lean_inc(v_v_2134_);
lean_inc(v_k_2133_);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_l_2119_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; lean_object* v_unused_2173_; 
v_unused_2169_ = lean_ctor_get(v_l_2119_, 4);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_l_2119_, 3);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_l_2119_, 2);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_l_2119_, 1);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_l_2119_, 0);
lean_dec(v_unused_2173_);
v___x_2142_ = v_l_2119_;
v_isShared_2143_ = v_isSharedCheck_2168_;
goto v_resetjp_2141_;
}
else
{
lean_dec(v_l_2119_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2168_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2158_; 
v___x_2144_ = lean_nat_add(v___x_2114_, v_size_2115_);
v___x_2145_ = lean_nat_add(v___x_2144_, v_size_2116_);
lean_dec(v_size_2116_);
if (lean_obj_tag(v_l_2135_) == 0)
{
lean_object* v_size_2166_; 
v_size_2166_ = lean_ctor_get(v_l_2135_, 0);
lean_inc(v_size_2166_);
v___y_2158_ = v_size_2166_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v___y_2158_ = v___x_2167_;
goto v___jp_2157_;
}
v___jp_2146_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_nat_add(v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 4, v_r_2120_);
lean_ctor_set(v___x_2142_, 3, v_r_2136_);
lean_ctor_set(v___x_2142_, 2, v_v_2118_);
lean_ctor_set(v___x_2142_, 1, v_k_2117_);
lean_ctor_set(v___x_2142_, 0, v___x_2150_);
v___x_2152_ = v___x_2142_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2117_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2118_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_r_2136_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_r_2120_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 4, v___x_2152_);
lean_ctor_set(v___x_2130_, 3, v___y_2147_);
lean_ctor_set(v___x_2130_, 2, v_v_2134_);
lean_ctor_set(v___x_2130_, 1, v_k_2133_);
lean_ctor_set(v___x_2130_, 0, v___x_2145_);
v___x_2154_ = v___x_2130_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v___y_2147_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
v___jp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_nat_add(v___x_2144_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec(v___x_2144_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_l_2135_);
lean_ctor_set(v___x_1970_, 0, v___x_2159_);
v___x_2161_ = v___x_1970_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_l_2135_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_nat_add(v___x_2114_, v_size_2137_);
if (lean_obj_tag(v_r_2136_) == 0)
{
lean_object* v_size_2163_; 
v_size_2163_ = lean_ctor_get(v_r_2136_, 0);
lean_inc(v_size_2163_);
v___y_2147_ = v___x_2161_;
v___y_2148_ = v___x_2162_;
v___y_2149_ = v_size_2163_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_unsigned_to_nat(0u);
v___y_2147_ = v___x_2161_;
v___y_2148_ = v___x_2162_;
v___y_2149_ = v___x_2164_;
goto v___jp_2146_;
}
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_del_object(v___x_1970_);
v___x_2174_ = lean_nat_add(v___x_2114_, v_size_2115_);
v___x_2175_ = lean_nat_add(v___x_2174_, v_size_2116_);
lean_dec(v_size_2116_);
v___x_2176_ = lean_nat_add(v___x_2174_, v_size_2132_);
lean_dec(v___x_2174_);
lean_inc_ref(v_l_1967_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 4, v_l_2119_);
lean_ctor_set(v___x_2130_, 3, v_l_1967_);
lean_ctor_set(v___x_2130_, 2, v_v_1966_);
lean_ctor_set(v___x_2130_, 1, v_k_1965_);
lean_ctor_set(v___x_2130_, 0, v___x_2176_);
v___x_2178_ = v___x_2130_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_l_2119_);
v___x_2178_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_isSharedCheck_2185_ = !lean_is_exclusive(v_l_1967_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2186_ = lean_ctor_get(v_l_1967_, 4);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_l_1967_, 3);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_l_1967_, 2);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_l_1967_, 1);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_1967_, 0);
lean_dec(v_unused_2190_);
v___x_2180_ = v_l_1967_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v_l_1967_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 4, v_r_2120_);
lean_ctor_set(v___x_2180_, 3, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v_v_2118_);
lean_ctor_set(v___x_2180_, 1, v_k_2117_);
lean_ctor_set(v___x_2180_, 0, v___x_2175_);
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_k_2117_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_v_2118_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_r_2120_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2198_; 
v_l_2198_ = lean_ctor_get(v_impl_2113_, 3);
lean_inc(v_l_2198_);
if (lean_obj_tag(v_l_2198_) == 0)
{
lean_object* v_r_2199_; lean_object* v_k_2200_; lean_object* v_v_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2224_; 
v_r_2199_ = lean_ctor_get(v_impl_2113_, 4);
v_k_2200_ = lean_ctor_get(v_impl_2113_, 1);
v_v_2201_ = lean_ctor_get(v_impl_2113_, 2);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_impl_2113_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; 
v_unused_2225_ = lean_ctor_get(v_impl_2113_, 3);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_impl_2113_, 0);
lean_dec(v_unused_2226_);
v___x_2203_ = v_impl_2113_;
v_isShared_2204_ = v_isSharedCheck_2224_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_r_2199_);
lean_inc(v_v_2201_);
lean_inc(v_k_2200_);
lean_dec(v_impl_2113_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2224_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2220_; 
v_k_2205_ = lean_ctor_get(v_l_2198_, 1);
v_v_2206_ = lean_ctor_get(v_l_2198_, 2);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_l_2198_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; lean_object* v_unused_2223_; 
v_unused_2221_ = lean_ctor_get(v_l_2198_, 4);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_l_2198_, 3);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_l_2198_, 0);
lean_dec(v_unused_2223_);
v___x_2208_ = v_l_2198_;
v_isShared_2209_ = v_isSharedCheck_2220_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_v_2206_);
lean_inc(v_k_2205_);
lean_dec(v_l_2198_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2220_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2199_, 2);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 4, v_r_2199_);
lean_ctor_set(v___x_2208_, 3, v_r_2199_);
lean_ctor_set(v___x_2208_, 2, v_v_1966_);
lean_ctor_set(v___x_2208_, 1, v_k_1965_);
lean_ctor_set(v___x_2208_, 0, v___x_2114_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_r_2199_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_r_2199_);
v___x_2212_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
lean_inc(v_r_2199_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 3, v_r_2199_);
lean_ctor_set(v___x_2203_, 0, v___x_2114_);
v___x_2214_ = v___x_2203_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_k_2200_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_v_2201_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_r_2199_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v_r_2199_);
v___x_2214_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2216_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_2214_);
lean_ctor_set(v___x_1970_, 3, v___x_2212_);
lean_ctor_set(v___x_1970_, 2, v_v_2206_);
lean_ctor_set(v___x_1970_, 1, v_k_2205_);
lean_ctor_set(v___x_1970_, 0, v___x_2210_);
v___x_2216_ = v___x_1970_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
else
{
lean_object* v_r_2227_; 
v_r_2227_ = lean_ctor_get(v_impl_2113_, 4);
lean_inc(v_r_2227_);
if (lean_obj_tag(v_r_2227_) == 0)
{
lean_object* v_k_2228_; lean_object* v_v_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2240_; 
v_k_2228_ = lean_ctor_get(v_impl_2113_, 1);
v_v_2229_ = lean_ctor_get(v_impl_2113_, 2);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_impl_2113_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; lean_object* v_unused_2242_; lean_object* v_unused_2243_; 
v_unused_2241_ = lean_ctor_get(v_impl_2113_, 4);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_impl_2113_, 3);
lean_dec(v_unused_2242_);
v_unused_2243_ = lean_ctor_get(v_impl_2113_, 0);
lean_dec(v_unused_2243_);
v___x_2231_ = v_impl_2113_;
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_v_2229_);
lean_inc(v_k_2228_);
lean_dec(v_impl_2113_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_unsigned_to_nat(3u);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 4, v_l_2198_);
lean_ctor_set(v___x_2231_, 2, v_v_1966_);
lean_ctor_set(v___x_2231_, 1, v_k_1965_);
lean_ctor_set(v___x_2231_, 0, v___x_2114_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_l_2198_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_l_2198_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_r_2227_);
lean_ctor_set(v___x_1970_, 3, v___x_2235_);
lean_ctor_set(v___x_1970_, 2, v_v_2229_);
lean_ctor_set(v___x_1970_, 1, v_k_2228_);
lean_ctor_set(v___x_1970_, 0, v___x_2233_);
v___x_2237_ = v___x_1970_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_r_2227_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = lean_unsigned_to_nat(2u);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v_impl_2113_);
lean_ctor_set(v___x_1970_, 3, v_r_2227_);
lean_ctor_set(v___x_1970_, 0, v___x_2244_);
v___x_2246_ = v___x_1970_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_r_2227_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_impl_2113_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
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
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_k_1961_);
lean_ctor_set(v___x_2250_, 2, v_v_1962_);
lean_ctor_set(v___x_2250_, 3, v_t_1963_);
lean_ctor_set(v___x_2250_, 4, v_t_1963_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2251_, lean_object* v_x_2252_){
_start:
{
if (lean_obj_tag(v_x_2252_) == 0)
{
lean_object* v_k_2253_; lean_object* v_v_2254_; lean_object* v_l_2255_; lean_object* v_r_2256_; lean_object* v___x_2257_; 
v_k_2253_ = lean_ctor_get(v_x_2252_, 1);
lean_inc(v_k_2253_);
v_v_2254_ = lean_ctor_get(v_x_2252_, 2);
lean_inc(v_v_2254_);
v_l_2255_ = lean_ctor_get(v_x_2252_, 3);
lean_inc(v_l_2255_);
v_r_2256_ = lean_ctor_get(v_x_2252_, 4);
lean_inc(v_r_2256_);
lean_dec_ref_known(v_x_2252_, 5);
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2251_, v_l_2255_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_dec(v_r_2256_);
lean_dec(v_v_2254_);
lean_dec(v_k_2253_);
return v___x_2257_;
}
else
{
if (lean_obj_tag(v_v_2254_) == 4)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2373_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2373_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2373_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_elems_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; uint8_t v___x_2266_; 
v_elems_2262_ = lean_ctor_get(v_v_2254_, 0);
lean_inc_ref(v_elems_2262_);
lean_dec_ref_known(v_v_2254_, 1);
v___x_2263_ = lean_array_get_size(v_elems_2262_);
v___x_2264_ = lean_unsigned_to_nat(8u);
v___x_2265_ = lean_nat_dec_eq(v___x_2263_, v___x_2264_);
v___x_2266_ = lean_bool_not(v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_del_object(v___x_2260_);
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2268_);
lean_inc(v___x_2269_);
v___x_2270_ = l_Lean_Json_getNat_x3f(v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2279_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2280_);
lean_inc(v___x_2281_);
v___x_2282_ = l_Lean_Json_getNat_x3f(v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2291_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2292_ = lean_unsigned_to_nat(2u);
v___x_2293_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2292_);
lean_inc(v___x_2293_);
v___x_2294_ = l_Lean_Json_getNat_x3f(v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_a_2303_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2304_ = lean_unsigned_to_nat(3u);
v___x_2305_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2304_);
lean_inc(v___x_2305_);
v___x_2306_ = l_Lean_Json_getNat_x3f(v___x_2305_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_a_2303_);
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_a_2315_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2316_ = lean_unsigned_to_nat(4u);
v___x_2317_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2316_);
lean_inc(v___x_2317_);
v___x_2318_ = l_Lean_Json_getNat_x3f(v___x_2317_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2315_);
lean_dec(v_a_2303_);
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2327_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2328_ = lean_unsigned_to_nat(5u);
v___x_2329_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2328_);
lean_inc(v___x_2329_);
v___x_2330_ = l_Lean_Json_getNat_x3f(v___x_2329_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2327_);
lean_dec(v_a_2315_);
lean_dec(v_a_2303_);
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2339_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2340_ = lean_unsigned_to_nat(6u);
v___x_2341_ = lean_array_get_borrowed(v___x_2267_, v_elems_2262_, v___x_2340_);
lean_inc(v___x_2341_);
v___x_2342_ = l_Lean_Json_getNat_x3f(v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2339_);
lean_dec(v_a_2327_);
lean_dec(v_a_2315_);
lean_dec(v_a_2303_);
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_a_2351_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2352_ = lean_unsigned_to_nat(7u);
v___x_2353_ = lean_array_get(v___x_2267_, v_elems_2262_, v___x_2352_);
lean_dec_ref(v_elems_2262_);
v___x_2354_ = l_Lean_Json_getNat_x3f(v___x_2353_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_a_2351_);
lean_dec(v_a_2339_);
lean_dec(v_a_2327_);
lean_dec(v_a_2315_);
lean_dec(v_a_2303_);
lean_dec(v_a_2291_);
lean_dec(v_a_2279_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_a_2363_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2364_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2279_);
lean_ctor_set(v___x_2364_, 1, v_a_2291_);
lean_ctor_set(v___x_2364_, 2, v_a_2303_);
lean_ctor_set(v___x_2364_, 3, v_a_2315_);
lean_ctor_set(v___x_2364_, 4, v_a_2327_);
lean_ctor_set(v___x_2364_, 5, v_a_2339_);
lean_ctor_set(v___x_2364_, 6, v_a_2351_);
lean_ctor_set(v___x_2364_, 7, v_a_2363_);
v___x_2365_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2253_, v___x_2364_, v_a_2258_);
v_init_2251_ = v___x_2365_;
v_x_2252_ = v_r_2256_;
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
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_dec_ref(v_elems_2262_);
lean_dec(v_a_2258_);
lean_dec(v_r_2256_);
lean_dec(v_k_2253_);
v___x_2367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2368_ = l_Nat_reprFast(v___x_2263_);
v___x_2369_ = lean_string_append(v___x_2367_, v___x_2368_);
lean_dec_ref(v___x_2368_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2369_);
v___x_2371_ = v___x_2260_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v___x_2374_; 
lean_dec_ref_known(v___x_2257_, 1);
lean_dec(v_r_2256_);
lean_dec(v_v_2254_);
lean_dec(v_k_2253_);
v___x_2374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2374_;
}
}
}
else
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_init_2251_);
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2376_, lean_object* v_k_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = l_Lean_Json_getObjValD(v_j_2376_, v_k_2377_);
v___x_2379_ = l_Lean_Json_getObj_x3f(v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2388_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2389_ = lean_box(1);
v___x_2390_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2389_, v_a_2388_);
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2391_, lean_object* v_k_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2391_, v_k_2392_);
lean_dec_ref(v_k_2392_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2394_, size_t v_i_2395_, lean_object* v_bs_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_usize_dec_lt(v_i_2395_, v_sz_2394_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_bs_2396_);
return v___x_2398_;
}
else
{
lean_object* v_v_2399_; lean_object* v___x_2400_; lean_object* v_bs_x27_2401_; size_t v___x_2402_; size_t v___x_2403_; lean_object* v___x_2404_; 
v_v_2399_ = lean_array_uget(v_bs_2396_, v_i_2395_);
v___x_2400_ = lean_unsigned_to_nat(0u);
v_bs_x27_2401_ = lean_array_uset(v_bs_2396_, v_i_2395_, v___x_2400_);
v___x_2402_ = ((size_t)1ULL);
v___x_2403_ = lean_usize_add(v_i_2395_, v___x_2402_);
v___x_2404_ = lean_array_uset(v_bs_x27_2401_, v_i_2395_, v_v_2399_);
v_i_2395_ = v___x_2403_;
v_bs_2396_ = v___x_2404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2406_, lean_object* v_i_2407_, lean_object* v_bs_2408_){
_start:
{
size_t v_sz_boxed_2409_; size_t v_i_boxed_2410_; lean_object* v_res_2411_; 
v_sz_boxed_2409_ = lean_unbox_usize(v_sz_2406_);
lean_dec(v_sz_2406_);
v_i_boxed_2410_ = lean_unbox_usize(v_i_2407_);
lean_dec(v_i_2407_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2409_, v_i_boxed_2410_, v_bs_2408_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2412_){
_start:
{
if (lean_obj_tag(v_x_2412_) == 4)
{
lean_object* v_elems_2413_; size_t v_sz_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v_elems_2413_ = lean_ctor_get(v_x_2412_, 0);
lean_inc_ref(v_elems_2413_);
lean_dec_ref_known(v_x_2412_, 1);
v_sz_2414_ = lean_array_size(v_elems_2413_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2414_, v___x_2415_, v_elems_2413_);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2417_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2418_ = lean_unsigned_to_nat(80u);
v___x_2419_ = l_Lean_Json_pretty(v_x_2412_, v___x_2418_);
v___x_2420_ = lean_string_append(v___x_2417_, v___x_2419_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2422_ = lean_string_append(v___x_2420_, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2426_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_a_2437_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2439_ = v___x_2428_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2428_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2446_, lean_object* v_k_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = l_Lean_Json_getObjValD(v_j_2446_, v_k_2447_);
v___x_2449_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2450_, lean_object* v_k_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2450_, v_k_2451_);
lean_dec_ref(v_k_2451_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2453_, lean_object* v_v_2454_, lean_object* v_t_2455_){
_start:
{
if (lean_obj_tag(v_t_2455_) == 0)
{
lean_object* v_size_2456_; lean_object* v_k_2457_; lean_object* v_v_2458_; lean_object* v_l_2459_; lean_object* v_r_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2740_; 
v_size_2456_ = lean_ctor_get(v_t_2455_, 0);
v_k_2457_ = lean_ctor_get(v_t_2455_, 1);
v_v_2458_ = lean_ctor_get(v_t_2455_, 2);
v_l_2459_ = lean_ctor_get(v_t_2455_, 3);
v_r_2460_ = lean_ctor_get(v_t_2455_, 4);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_t_2455_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2462_ = v_t_2455_;
v_isShared_2463_ = v_isSharedCheck_2740_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_r_2460_);
lean_inc(v_l_2459_);
lean_inc(v_v_2458_);
lean_inc(v_k_2457_);
lean_inc(v_size_2456_);
lean_dec(v_t_2455_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2740_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2453_, v_k_2457_);
switch(v___x_2464_)
{
case 0:
{
lean_object* v_impl_2465_; lean_object* v___x_2466_; 
lean_dec(v_size_2456_);
v_impl_2465_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2453_, v_v_2454_, v_l_2459_);
v___x_2466_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2460_) == 0)
{
lean_object* v_size_2467_; lean_object* v_size_2468_; lean_object* v_k_2469_; lean_object* v_v_2470_; lean_object* v_l_2471_; lean_object* v_r_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_size_2467_ = lean_ctor_get(v_r_2460_, 0);
v_size_2468_ = lean_ctor_get(v_impl_2465_, 0);
lean_inc(v_size_2468_);
v_k_2469_ = lean_ctor_get(v_impl_2465_, 1);
lean_inc(v_k_2469_);
v_v_2470_ = lean_ctor_get(v_impl_2465_, 2);
lean_inc(v_v_2470_);
v_l_2471_ = lean_ctor_get(v_impl_2465_, 3);
lean_inc(v_l_2471_);
v_r_2472_ = lean_ctor_get(v_impl_2465_, 4);
lean_inc(v_r_2472_);
v___x_2473_ = lean_unsigned_to_nat(3u);
v___x_2474_ = lean_nat_mul(v___x_2473_, v_size_2467_);
v___x_2475_ = lean_nat_dec_lt(v___x_2474_, v_size_2468_);
lean_dec(v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_dec(v_r_2472_);
lean_dec(v_l_2471_);
lean_dec(v_v_2470_);
lean_dec(v_k_2469_);
v___x_2476_ = lean_nat_add(v___x_2466_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2477_ = lean_nat_add(v___x_2476_, v_size_2467_);
lean_dec(v___x_2476_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 3, v_impl_2465_);
lean_ctor_set(v___x_2462_, 0, v___x_2477_);
v___x_2479_ = v___x_2462_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_impl_2465_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_r_2460_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
else
{
lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2546_; 
v_isSharedCheck_2546_ = !lean_is_exclusive(v_impl_2465_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; lean_object* v_unused_2551_; 
v_unused_2547_ = lean_ctor_get(v_impl_2465_, 4);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_impl_2465_, 3);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_impl_2465_, 2);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_impl_2465_, 1);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_impl_2465_, 0);
lean_dec(v_unused_2551_);
v___x_2482_ = v_impl_2465_;
v_isShared_2483_ = v_isSharedCheck_2546_;
goto v_resetjp_2481_;
}
else
{
lean_dec(v_impl_2465_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2546_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_size_2484_; lean_object* v_size_2485_; lean_object* v_k_2486_; lean_object* v_v_2487_; lean_object* v_l_2488_; lean_object* v_r_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_size_2484_ = lean_ctor_get(v_l_2471_, 0);
v_size_2485_ = lean_ctor_get(v_r_2472_, 0);
v_k_2486_ = lean_ctor_get(v_r_2472_, 1);
v_v_2487_ = lean_ctor_get(v_r_2472_, 2);
v_l_2488_ = lean_ctor_get(v_r_2472_, 3);
v_r_2489_ = lean_ctor_get(v_r_2472_, 4);
v___x_2490_ = lean_unsigned_to_nat(2u);
v___x_2491_ = lean_nat_mul(v___x_2490_, v_size_2484_);
v___x_2492_ = lean_nat_dec_lt(v_size_2485_, v___x_2491_);
lean_dec(v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2521_; 
lean_inc(v_r_2489_);
lean_inc(v_l_2488_);
lean_inc(v_v_2487_);
lean_inc(v_k_2486_);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_r_2472_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; lean_object* v_unused_2523_; lean_object* v_unused_2524_; lean_object* v_unused_2525_; lean_object* v_unused_2526_; 
v_unused_2522_ = lean_ctor_get(v_r_2472_, 4);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_r_2472_, 3);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_r_2472_, 2);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_r_2472_, 1);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v_r_2472_, 0);
lean_dec(v_unused_2526_);
v___x_2494_ = v_r_2472_;
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
else
{
lean_dec(v_r_2472_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2521_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___x_2509_; lean_object* v___y_2511_; 
v___x_2496_ = lean_nat_add(v___x_2466_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2497_ = lean_nat_add(v___x_2496_, v_size_2467_);
lean_dec(v___x_2496_);
v___x_2509_ = lean_nat_add(v___x_2466_, v_size_2484_);
if (lean_obj_tag(v_l_2488_) == 0)
{
lean_object* v_size_2519_; 
v_size_2519_ = lean_ctor_get(v_l_2488_, 0);
lean_inc(v_size_2519_);
v___y_2511_ = v_size_2519_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v___y_2511_ = v___x_2520_;
goto v___jp_2510_;
}
v___jp_2498_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_nat_add(v___y_2499_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec(v___y_2499_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 4, v_r_2460_);
lean_ctor_set(v___x_2494_, 3, v_r_2489_);
lean_ctor_set(v___x_2494_, 2, v_v_2458_);
lean_ctor_set(v___x_2494_, 1, v_k_2457_);
lean_ctor_set(v___x_2494_, 0, v___x_2502_);
v___x_2504_ = v___x_2494_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_r_2489_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_r_2460_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 4, v___x_2504_);
lean_ctor_set(v___x_2482_, 3, v___y_2500_);
lean_ctor_set(v___x_2482_, 2, v_v_2487_);
lean_ctor_set(v___x_2482_, 1, v_k_2486_);
lean_ctor_set(v___x_2482_, 0, v___x_2497_);
v___x_2506_ = v___x_2482_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_k_2486_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_v_2487_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v___y_2500_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2512_ = lean_nat_add(v___x_2509_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec(v___x_2509_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_l_2488_);
lean_ctor_set(v___x_2462_, 3, v_l_2471_);
lean_ctor_set(v___x_2462_, 2, v_v_2470_);
lean_ctor_set(v___x_2462_, 1, v_k_2469_);
lean_ctor_set(v___x_2462_, 0, v___x_2512_);
v___x_2514_ = v___x_2462_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_l_2488_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_nat_add(v___x_2466_, v_size_2467_);
if (lean_obj_tag(v_r_2489_) == 0)
{
lean_object* v_size_2516_; 
v_size_2516_ = lean_ctor_get(v_r_2489_, 0);
lean_inc(v_size_2516_);
v___y_2499_ = v___x_2515_;
v___y_2500_ = v___x_2514_;
v___y_2501_ = v_size_2516_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_unsigned_to_nat(0u);
v___y_2499_ = v___x_2515_;
v___y_2500_ = v___x_2514_;
v___y_2501_ = v___x_2517_;
goto v___jp_2498_;
}
}
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
lean_del_object(v___x_2462_);
v___x_2527_ = lean_nat_add(v___x_2466_, v_size_2468_);
lean_dec(v_size_2468_);
v___x_2528_ = lean_nat_add(v___x_2527_, v_size_2467_);
lean_dec(v___x_2527_);
v___x_2529_ = lean_nat_add(v___x_2466_, v_size_2467_);
v___x_2530_ = lean_nat_add(v___x_2529_, v_size_2485_);
lean_dec(v___x_2529_);
lean_inc_ref(v_r_2460_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 4, v_r_2460_);
lean_ctor_set(v___x_2482_, 3, v_r_2472_);
lean_ctor_set(v___x_2482_, 2, v_v_2458_);
lean_ctor_set(v___x_2482_, 1, v_k_2457_);
lean_ctor_set(v___x_2482_, 0, v___x_2530_);
v___x_2532_ = v___x_2482_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_r_2460_);
v___x_2532_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_isSharedCheck_2539_ = !lean_is_exclusive(v_r_2460_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; lean_object* v_unused_2544_; 
v_unused_2540_ = lean_ctor_get(v_r_2460_, 4);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_r_2460_, 3);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_r_2460_, 2);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_r_2460_, 1);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_r_2460_, 0);
lean_dec(v_unused_2544_);
v___x_2534_ = v_r_2460_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_dec(v_r_2460_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 4, v___x_2532_);
lean_ctor_set(v___x_2534_, 3, v_l_2471_);
lean_ctor_set(v___x_2534_, 2, v_v_2470_);
lean_ctor_set(v___x_2534_, 1, v_k_2469_);
lean_ctor_set(v___x_2534_, 0, v___x_2528_);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2469_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2470_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v___x_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2552_; 
v_l_2552_ = lean_ctor_get(v_impl_2465_, 3);
lean_inc(v_l_2552_);
if (lean_obj_tag(v_l_2552_) == 0)
{
lean_object* v_r_2553_; lean_object* v_k_2554_; lean_object* v_v_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2566_; 
v_r_2553_ = lean_ctor_get(v_impl_2465_, 4);
v_k_2554_ = lean_ctor_get(v_impl_2465_, 1);
v_v_2555_ = lean_ctor_get(v_impl_2465_, 2);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_impl_2465_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2567_ = lean_ctor_get(v_impl_2465_, 3);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_impl_2465_, 0);
lean_dec(v_unused_2568_);
v___x_2557_ = v_impl_2465_;
v_isShared_2558_ = v_isSharedCheck_2566_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_r_2553_);
lean_inc(v_v_2555_);
lean_inc(v_k_2554_);
lean_dec(v_impl_2465_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2566_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2553_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 3, v_r_2553_);
lean_ctor_set(v___x_2557_, 2, v_v_2458_);
lean_ctor_set(v___x_2557_, 1, v_k_2457_);
lean_ctor_set(v___x_2557_, 0, v___x_2466_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_r_2553_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_r_2553_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2563_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v___x_2561_);
lean_ctor_set(v___x_2462_, 3, v_l_2552_);
lean_ctor_set(v___x_2462_, 2, v_v_2555_);
lean_ctor_set(v___x_2462_, 1, v_k_2554_);
lean_ctor_set(v___x_2462_, 0, v___x_2559_);
v___x_2563_ = v___x_2462_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_k_2554_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_v_2555_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_l_2552_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_r_2569_; 
v_r_2569_ = lean_ctor_get(v_impl_2465_, 4);
lean_inc(v_r_2569_);
if (lean_obj_tag(v_r_2569_) == 0)
{
lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2594_; 
v_k_2570_ = lean_ctor_get(v_impl_2465_, 1);
v_v_2571_ = lean_ctor_get(v_impl_2465_, 2);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_impl_2465_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; lean_object* v_unused_2596_; lean_object* v_unused_2597_; 
v_unused_2595_ = lean_ctor_get(v_impl_2465_, 4);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_impl_2465_, 3);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_impl_2465_, 0);
lean_dec(v_unused_2597_);
v___x_2573_ = v_impl_2465_;
v_isShared_2574_ = v_isSharedCheck_2594_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_v_2571_);
lean_inc(v_k_2570_);
lean_dec(v_impl_2465_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2594_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_k_2575_; lean_object* v_v_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2590_; 
v_k_2575_ = lean_ctor_get(v_r_2569_, 1);
v_v_2576_ = lean_ctor_get(v_r_2569_, 2);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_r_2569_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; lean_object* v_unused_2592_; lean_object* v_unused_2593_; 
v_unused_2591_ = lean_ctor_get(v_r_2569_, 4);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_r_2569_, 3);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_r_2569_, 0);
lean_dec(v_unused_2593_);
v___x_2578_ = v_r_2569_;
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_v_2576_);
lean_inc(v_k_2575_);
lean_dec(v_r_2569_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_unsigned_to_nat(3u);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v_l_2552_);
lean_ctor_set(v___x_2578_, 3, v_l_2552_);
lean_ctor_set(v___x_2578_, 2, v_v_2571_);
lean_ctor_set(v___x_2578_, 1, v_k_2570_);
lean_ctor_set(v___x_2578_, 0, v___x_2466_);
v___x_2582_ = v___x_2578_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_l_2552_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_l_2552_);
v___x_2582_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 4, v_l_2552_);
lean_ctor_set(v___x_2573_, 2, v_v_2458_);
lean_ctor_set(v___x_2573_, 1, v_k_2457_);
lean_ctor_set(v___x_2573_, 0, v___x_2466_);
v___x_2584_ = v___x_2573_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v_l_2552_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v_l_2552_);
v___x_2584_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2586_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v___x_2584_);
lean_ctor_set(v___x_2462_, 3, v___x_2582_);
lean_ctor_set(v___x_2462_, 2, v_v_2576_);
lean_ctor_set(v___x_2462_, 1, v_k_2575_);
lean_ctor_set(v___x_2462_, 0, v___x_2580_);
v___x_2586_ = v___x_2462_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_k_2575_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_v_2576_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_unsigned_to_nat(2u);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_r_2569_);
lean_ctor_set(v___x_2462_, 3, v_impl_2465_);
lean_ctor_set(v___x_2462_, 0, v___x_2598_);
v___x_2600_ = v___x_2462_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_impl_2465_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2569_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2603_; 
lean_dec(v_v_2458_);
lean_dec(v_k_2457_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 2, v_v_2454_);
lean_ctor_set(v___x_2462_, 1, v_k_2453_);
v___x_2603_ = v___x_2462_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_size_2456_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2453_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2454_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_l_2459_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_r_2460_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
default: 
{
lean_object* v_impl_2605_; lean_object* v___x_2606_; 
lean_dec(v_size_2456_);
v_impl_2605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2453_, v_v_2454_, v_r_2460_);
v___x_2606_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2459_) == 0)
{
lean_object* v_size_2607_; lean_object* v_size_2608_; lean_object* v_k_2609_; lean_object* v_v_2610_; lean_object* v_l_2611_; lean_object* v_r_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v_size_2607_ = lean_ctor_get(v_l_2459_, 0);
v_size_2608_ = lean_ctor_get(v_impl_2605_, 0);
lean_inc(v_size_2608_);
v_k_2609_ = lean_ctor_get(v_impl_2605_, 1);
lean_inc(v_k_2609_);
v_v_2610_ = lean_ctor_get(v_impl_2605_, 2);
lean_inc(v_v_2610_);
v_l_2611_ = lean_ctor_get(v_impl_2605_, 3);
lean_inc(v_l_2611_);
v_r_2612_ = lean_ctor_get(v_impl_2605_, 4);
lean_inc(v_r_2612_);
v___x_2613_ = lean_unsigned_to_nat(3u);
v___x_2614_ = lean_nat_mul(v___x_2613_, v_size_2607_);
v___x_2615_ = lean_nat_dec_lt(v___x_2614_, v_size_2608_);
lean_dec(v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec(v_r_2612_);
lean_dec(v_l_2611_);
lean_dec(v_v_2610_);
lean_dec(v_k_2609_);
v___x_2616_ = lean_nat_add(v___x_2606_, v_size_2607_);
v___x_2617_ = lean_nat_add(v___x_2616_, v_size_2608_);
lean_dec(v_size_2608_);
lean_dec(v___x_2616_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_impl_2605_);
lean_ctor_set(v___x_2462_, 0, v___x_2617_);
v___x_2619_ = v___x_2462_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_l_2459_);
lean_ctor_set(v_reuseFailAlloc_2620_, 4, v_impl_2605_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2684_; 
v_isSharedCheck_2684_ = !lean_is_exclusive(v_impl_2605_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; 
v_unused_2685_ = lean_ctor_get(v_impl_2605_, 4);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_impl_2605_, 3);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_impl_2605_, 2);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_impl_2605_, 1);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_impl_2605_, 0);
lean_dec(v_unused_2689_);
v___x_2622_ = v_impl_2605_;
v_isShared_2623_ = v_isSharedCheck_2684_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_impl_2605_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2684_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v_size_2624_; lean_object* v_k_2625_; lean_object* v_v_2626_; lean_object* v_l_2627_; lean_object* v_r_2628_; lean_object* v_size_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_size_2624_ = lean_ctor_get(v_l_2611_, 0);
v_k_2625_ = lean_ctor_get(v_l_2611_, 1);
v_v_2626_ = lean_ctor_get(v_l_2611_, 2);
v_l_2627_ = lean_ctor_get(v_l_2611_, 3);
v_r_2628_ = lean_ctor_get(v_l_2611_, 4);
v_size_2629_ = lean_ctor_get(v_r_2612_, 0);
v___x_2630_ = lean_unsigned_to_nat(2u);
v___x_2631_ = lean_nat_mul(v___x_2630_, v_size_2629_);
v___x_2632_ = lean_nat_dec_lt(v_size_2624_, v___x_2631_);
lean_dec(v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2660_; 
lean_inc(v_r_2628_);
lean_inc(v_l_2627_);
lean_inc(v_v_2626_);
lean_inc(v_k_2625_);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_l_2611_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; 
v_unused_2661_ = lean_ctor_get(v_l_2611_, 4);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_l_2611_, 3);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_l_2611_, 2);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_l_2611_, 1);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_l_2611_, 0);
lean_dec(v_unused_2665_);
v___x_2634_ = v_l_2611_;
v_isShared_2635_ = v_isSharedCheck_2660_;
goto v_resetjp_2633_;
}
else
{
lean_dec(v_l_2611_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2660_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2650_; 
v___x_2636_ = lean_nat_add(v___x_2606_, v_size_2607_);
v___x_2637_ = lean_nat_add(v___x_2636_, v_size_2608_);
lean_dec(v_size_2608_);
if (lean_obj_tag(v_l_2627_) == 0)
{
lean_object* v_size_2658_; 
v_size_2658_ = lean_ctor_get(v_l_2627_, 0);
lean_inc(v_size_2658_);
v___y_2650_ = v_size_2658_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___y_2650_ = v___x_2659_;
goto v___jp_2649_;
}
v___jp_2638_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_nat_add(v___y_2639_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec(v___y_2639_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 4, v_r_2612_);
lean_ctor_set(v___x_2634_, 3, v_r_2628_);
lean_ctor_set(v___x_2634_, 2, v_v_2610_);
lean_ctor_set(v___x_2634_, 1, v_k_2609_);
lean_ctor_set(v___x_2634_, 0, v___x_2642_);
v___x_2644_ = v___x_2634_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2609_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2610_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_r_2628_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_r_2612_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v___x_2644_);
lean_ctor_set(v___x_2622_, 3, v___y_2640_);
lean_ctor_set(v___x_2622_, 2, v_v_2626_);
lean_ctor_set(v___x_2622_, 1, v_k_2625_);
lean_ctor_set(v___x_2622_, 0, v___x_2637_);
v___x_2646_ = v___x_2622_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2625_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2626_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v___y_2640_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
v___jp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_nat_add(v___x_2636_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec(v___x_2636_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_l_2627_);
lean_ctor_set(v___x_2462_, 0, v___x_2651_);
v___x_2653_ = v___x_2462_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_l_2459_);
lean_ctor_set(v_reuseFailAlloc_2657_, 4, v_l_2627_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_nat_add(v___x_2606_, v_size_2629_);
if (lean_obj_tag(v_r_2628_) == 0)
{
lean_object* v_size_2655_; 
v_size_2655_ = lean_ctor_get(v_r_2628_, 0);
lean_inc(v_size_2655_);
v___y_2639_ = v___x_2654_;
v___y_2640_ = v___x_2653_;
v___y_2641_ = v_size_2655_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___y_2639_ = v___x_2654_;
v___y_2640_ = v___x_2653_;
v___y_2641_ = v___x_2656_;
goto v___jp_2638_;
}
}
}
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_del_object(v___x_2462_);
v___x_2666_ = lean_nat_add(v___x_2606_, v_size_2607_);
v___x_2667_ = lean_nat_add(v___x_2666_, v_size_2608_);
lean_dec(v_size_2608_);
v___x_2668_ = lean_nat_add(v___x_2666_, v_size_2624_);
lean_dec(v___x_2666_);
lean_inc_ref(v_l_2459_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_l_2611_);
lean_ctor_set(v___x_2622_, 3, v_l_2459_);
lean_ctor_set(v___x_2622_, 2, v_v_2458_);
lean_ctor_set(v___x_2622_, 1, v_k_2457_);
lean_ctor_set(v___x_2622_, 0, v___x_2668_);
v___x_2670_ = v___x_2622_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_l_2459_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_l_2611_);
v___x_2670_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_isSharedCheck_2677_ = !lean_is_exclusive(v_l_2459_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2678_ = lean_ctor_get(v_l_2459_, 4);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2459_, 3);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2459_, 2);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2459_, 1);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_l_2459_, 0);
lean_dec(v_unused_2682_);
v___x_2672_ = v_l_2459_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v_l_2459_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 4, v_r_2612_);
lean_ctor_set(v___x_2672_, 3, v___x_2670_);
lean_ctor_set(v___x_2672_, 2, v_v_2610_);
lean_ctor_set(v___x_2672_, 1, v_k_2609_);
lean_ctor_set(v___x_2672_, 0, v___x_2667_);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_k_2609_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_v_2610_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v_r_2612_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2690_; 
v_l_2690_ = lean_ctor_get(v_impl_2605_, 3);
lean_inc(v_l_2690_);
if (lean_obj_tag(v_l_2690_) == 0)
{
lean_object* v_r_2691_; lean_object* v_k_2692_; lean_object* v_v_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2716_; 
v_r_2691_ = lean_ctor_get(v_impl_2605_, 4);
v_k_2692_ = lean_ctor_get(v_impl_2605_, 1);
v_v_2693_ = lean_ctor_get(v_impl_2605_, 2);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_impl_2605_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; 
v_unused_2717_ = lean_ctor_get(v_impl_2605_, 3);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_impl_2605_, 0);
lean_dec(v_unused_2718_);
v___x_2695_ = v_impl_2605_;
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_r_2691_);
lean_inc(v_v_2693_);
lean_inc(v_k_2692_);
lean_dec(v_impl_2605_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_k_2697_; lean_object* v_v_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2712_; 
v_k_2697_ = lean_ctor_get(v_l_2690_, 1);
v_v_2698_ = lean_ctor_get(v_l_2690_, 2);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_l_2690_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2713_ = lean_ctor_get(v_l_2690_, 4);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_l_2690_, 3);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_l_2690_, 0);
lean_dec(v_unused_2715_);
v___x_2700_ = v_l_2690_;
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_v_2698_);
lean_inc(v_k_2697_);
lean_dec(v_l_2690_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2691_, 2);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 4, v_r_2691_);
lean_ctor_set(v___x_2700_, 3, v_r_2691_);
lean_ctor_set(v___x_2700_, 2, v_v_2458_);
lean_ctor_set(v___x_2700_, 1, v_k_2457_);
lean_ctor_set(v___x_2700_, 0, v___x_2606_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_r_2691_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_r_2691_);
v___x_2704_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
lean_inc(v_r_2691_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 3, v_r_2691_);
lean_ctor_set(v___x_2695_, 0, v___x_2606_);
v___x_2706_ = v___x_2695_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2692_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2693_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_r_2691_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_r_2691_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v___x_2706_);
lean_ctor_set(v___x_2462_, 3, v___x_2704_);
lean_ctor_set(v___x_2462_, 2, v_v_2698_);
lean_ctor_set(v___x_2462_, 1, v_k_2697_);
lean_ctor_set(v___x_2462_, 0, v___x_2702_);
v___x_2708_ = v___x_2462_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2697_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2698_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
}
else
{
lean_object* v_r_2719_; 
v_r_2719_ = lean_ctor_get(v_impl_2605_, 4);
lean_inc(v_r_2719_);
if (lean_obj_tag(v_r_2719_) == 0)
{
lean_object* v_k_2720_; lean_object* v_v_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2732_; 
v_k_2720_ = lean_ctor_get(v_impl_2605_, 1);
v_v_2721_ = lean_ctor_get(v_impl_2605_, 2);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_impl_2605_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2733_ = lean_ctor_get(v_impl_2605_, 4);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_impl_2605_, 3);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_impl_2605_, 0);
lean_dec(v_unused_2735_);
v___x_2723_ = v_impl_2605_;
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_v_2721_);
lean_inc(v_k_2720_);
lean_dec(v_impl_2605_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2732_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2725_ = lean_unsigned_to_nat(3u);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 4, v_l_2690_);
lean_ctor_set(v___x_2723_, 2, v_v_2458_);
lean_ctor_set(v___x_2723_, 1, v_k_2457_);
lean_ctor_set(v___x_2723_, 0, v___x_2606_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_l_2690_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_l_2690_);
v___x_2727_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2729_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_r_2719_);
lean_ctor_set(v___x_2462_, 3, v___x_2727_);
lean_ctor_set(v___x_2462_, 2, v_v_2721_);
lean_ctor_set(v___x_2462_, 1, v_k_2720_);
lean_ctor_set(v___x_2462_, 0, v___x_2725_);
v___x_2729_ = v___x_2462_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_r_2719_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_unsigned_to_nat(2u);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v_impl_2605_);
lean_ctor_set(v___x_2462_, 3, v_r_2719_);
lean_ctor_set(v___x_2462_, 0, v___x_2736_);
v___x_2738_ = v___x_2462_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_r_2719_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v_impl_2605_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
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
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
lean_ctor_set(v___x_2742_, 1, v_k_2453_);
lean_ctor_set(v___x_2742_, 2, v_v_2454_);
lean_ctor_set(v___x_2742_, 3, v_t_2455_);
lean_ctor_set(v___x_2742_, 4, v_t_2455_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2743_, size_t v_i_2744_, lean_object* v_bs_2745_){
_start:
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_bs_2745_);
return v___x_2747_;
}
else
{
lean_object* v_v_2748_; lean_object* v___x_2749_; lean_object* v_bs_x27_2750_; lean_object* v_a_2752_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2823_; 
v_v_2748_ = lean_array_uget(v_bs_2745_, v_i_2744_);
v___x_2749_ = lean_unsigned_to_nat(0u);
v_bs_x27_2750_ = lean_array_uset(v_bs_2745_, v_i_2744_, v___x_2749_);
v___x_2757_ = lean_array_get_size(v_v_2748_);
v___x_2758_ = lean_unsigned_to_nat(4u);
v___x_2823_ = lean_nat_dec_eq(v___x_2757_, v___x_2758_);
if (v___x_2823_ == 0)
{
if (v___x_2746_ == 0)
{
goto v___jp_2759_;
}
else
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_unsigned_to_nat(5u);
v___x_2825_ = lean_nat_dec_eq(v___x_2757_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec_ref(v_bs_x27_2750_);
lean_dec(v_v_2748_);
v___x_2826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2827_ = l_Nat_reprFast(v___x_2757_);
v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
else
{
goto v___jp_2759_;
}
}
}
else
{
goto v___jp_2759_;
}
v___jp_2751_:
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((size_t)1ULL);
v___x_2754_ = lean_usize_add(v_i_2744_, v___x_2753_);
v___x_2755_ = lean_array_uset(v_bs_x27_2750_, v_i_2744_, v_a_2752_);
v_i_2744_ = v___x_2754_;
v_bs_2745_ = v___x_2755_;
goto _start;
}
v___jp_2759_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_array_fget_borrowed(v_v_2748_, v___x_2749_);
lean_inc(v___x_2760_);
v___x_2761_ = l_Lean_Json_getNat_x3f(v___x_2760_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v_bs_x27_2750_);
lean_dec(v_v_2748_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_a_2770_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_array_fget_borrowed(v_v_2748_, v___x_2771_);
lean_inc(v___x_2772_);
v___x_2773_ = l_Lean_Json_getNat_x3f(v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2770_);
lean_dec_ref(v_bs_x27_2750_);
lean_dec(v_v_2748_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2783_ = lean_unsigned_to_nat(2u);
v___x_2784_ = lean_array_fget_borrowed(v_v_2748_, v___x_2783_);
lean_inc(v___x_2784_);
v___x_2785_ = l_Lean_Json_getNat_x3f(v___x_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2770_);
lean_dec_ref(v_bs_x27_2750_);
lean_dec(v_v_2748_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2795_ = lean_unsigned_to_nat(3u);
v___x_2796_ = lean_array_fget_borrowed(v_v_2748_, v___x_2795_);
lean_inc(v___x_2796_);
v___x_2797_ = l_Lean_Json_getNat_x3f(v___x_2796_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2782_);
lean_dec(v_a_2770_);
lean_dec_ref(v_bs_x27_2750_);
lean_dec(v_v_2748_);
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2807_ = lean_unsigned_to_nat(5u);
v___x_2808_ = lean_nat_dec_eq(v___x_2757_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec(v_v_2748_);
v___x_2809_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2810_, 0, v_a_2770_);
lean_ctor_set(v___x_2810_, 1, v_a_2782_);
lean_ctor_set(v___x_2810_, 2, v_a_2794_);
lean_ctor_set(v___x_2810_, 3, v_a_2806_);
lean_ctor_set(v___x_2810_, 4, v___x_2809_);
v_a_2752_ = v___x_2810_;
goto v___jp_2751_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_array_fget(v_v_2748_, v___x_2758_);
lean_dec(v_v_2748_);
v___x_2812_ = l_Lean_Json_getStr_x3f(v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2806_);
lean_dec(v_a_2794_);
lean_dec(v_a_2782_);
lean_dec(v_a_2770_);
lean_dec_ref(v_bs_x27_2750_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2770_);
lean_ctor_set(v___x_2822_, 1, v_a_2782_);
lean_ctor_set(v___x_2822_, 2, v_a_2794_);
lean_ctor_set(v___x_2822_, 3, v_a_2806_);
lean_ctor_set(v___x_2822_, 4, v_a_2821_);
v_a_2752_ = v___x_2822_;
goto v___jp_2751_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_bs_2832_){
_start:
{
size_t v_sz_boxed_2833_; size_t v_i_boxed_2834_; lean_object* v_res_2835_; 
v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2833_, v_i_boxed_2834_, v_bs_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2836_, size_t v_i_2837_, lean_object* v_bs_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_lt(v_i_2837_, v_sz_2836_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_bs_2838_);
return v___x_2840_;
}
else
{
lean_object* v_v_2841_; lean_object* v___x_2842_; 
v_v_2841_ = lean_array_uget_borrowed(v_bs_2838_, v_i_2837_);
lean_inc(v_v_2841_);
v___x_2842_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_bs_2838_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v_bs_x27_2853_; size_t v___x_2854_; size_t v___x_2855_; lean_object* v___x_2856_; 
v_a_2851_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2852_ = lean_unsigned_to_nat(0u);
v_bs_x27_2853_ = lean_array_uset(v_bs_2838_, v_i_2837_, v___x_2852_);
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_add(v_i_2837_, v___x_2854_);
v___x_2856_ = lean_array_uset(v_bs_x27_2853_, v_i_2837_, v_a_2851_);
v_i_2837_ = v___x_2855_;
v_bs_2838_ = v___x_2856_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_bs_2860_){
_start:
{
size_t v_sz_boxed_2861_; size_t v_i_boxed_2862_; lean_object* v_res_2863_; 
v_sz_boxed_2861_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2862_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2861_, v_i_boxed_2862_, v_bs_2860_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2864_){
_start:
{
if (lean_obj_tag(v_x_2864_) == 4)
{
lean_object* v_elems_2865_; size_t v_sz_2866_; size_t v___x_2867_; lean_object* v___x_2868_; 
v_elems_2865_ = lean_ctor_get(v_x_2864_, 0);
lean_inc_ref(v_elems_2865_);
lean_dec_ref_known(v_x_2864_, 1);
v_sz_2866_ = lean_array_size(v_elems_2865_);
v___x_2867_ = ((size_t)0ULL);
v___x_2868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2866_, v___x_2867_, v_elems_2865_);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2869_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2870_ = lean_unsigned_to_nat(80u);
v___x_2871_ = l_Lean_Json_pretty(v_x_2864_, v___x_2870_);
v___x_2872_ = lean_string_append(v___x_2869_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2876_, lean_object* v_k_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_Json_getObjValD(v_j_2876_, v_k_2877_);
v___x_2879_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2880_, lean_object* v_k_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2880_, v_k_2881_);
lean_dec_ref(v_k_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2883_, lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 0)
{
lean_object* v_k_2885_; lean_object* v_v_2886_; lean_object* v_l_2887_; lean_object* v_r_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_3048_; 
v_k_2885_ = lean_ctor_get(v_x_2884_, 1);
v_v_2886_ = lean_ctor_get(v_x_2884_, 2);
v_l_2887_ = lean_ctor_get(v_x_2884_, 3);
v_r_2888_ = lean_ctor_get(v_x_2884_, 4);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_x_2884_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v_x_2884_, 0);
lean_dec(v_unused_3049_);
v___x_2890_ = v_x_2884_;
v_isShared_2891_ = v_isSharedCheck_3048_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_r_2888_);
lean_inc(v_l_2887_);
lean_inc(v_v_2886_);
lean_inc(v_k_2885_);
lean_dec(v_x_2884_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_3048_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2883_, v_l_2887_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
lean_dec(v_k_2885_);
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_3047_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_3047_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_3047_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Json_parse(v_k_2885_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2897_, 1);
v___x_2907_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v_definition_x3f_2918_; lean_object* v_a_2946_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2916_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2950_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2886_);
v___x_2951_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2886_, v___x_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3046_; 
v_a_2960_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_2962_ = v___x_2951_;
v_isShared_2963_ = v_isSharedCheck_3046_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2951_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3046_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
if (lean_obj_tag(v_a_2960_) == 0)
{
lean_object* v___x_2964_; 
lean_del_object(v___x_2962_);
lean_del_object(v___x_2895_);
lean_del_object(v___x_2890_);
v___x_2964_ = lean_box(0);
v_definition_x3f_2918_ = v___x_2964_;
goto v___jp_2917_;
}
else
{
lean_object* v_val_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_3037_; 
v_val_2965_ = lean_ctor_get(v_a_2960_, 0);
lean_inc(v_val_2965_);
lean_dec_ref_known(v_a_2960_, 1);
v___x_2966_ = lean_array_get_size(v_val_2965_);
v___x_2967_ = lean_unsigned_to_nat(4u);
v___x_3037_ = lean_nat_dec_eq(v___x_2966_, v___x_2967_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = lean_unsigned_to_nat(5u);
v___x_3039_ = lean_nat_dec_eq(v___x_2966_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_dec(v_val_2965_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v___x_3040_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3041_ = l_Nat_reprFast(v___x_2966_);
v___x_3042_ = lean_string_append(v___x_3040_, v___x_3041_);
lean_dec_ref(v___x_3041_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 0);
lean_ctor_set(v___x_2962_, 0, v___x_3042_);
v___x_3044_ = v___x_2962_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_del_object(v___x_2962_);
goto v___jp_2968_;
}
}
else
{
lean_del_object(v___x_2962_);
goto v___jp_2968_;
}
v___jp_2968_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = lean_array_fget_borrowed(v_val_2965_, v___x_2969_);
lean_inc(v___x_2970_);
v___x_2971_ = l_Lean_Json_getNat_x3f(v___x_2970_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_val_2965_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2980_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2981_ = lean_unsigned_to_nat(1u);
v___x_2982_ = lean_array_fget_borrowed(v_val_2965_, v___x_2981_);
lean_inc(v___x_2982_);
v___x_2983_ = l_Lean_Json_getNat_x3f(v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2980_);
lean_dec(v_val_2965_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2992_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2993_ = lean_unsigned_to_nat(2u);
v___x_2994_ = lean_array_fget_borrowed(v_val_2965_, v___x_2993_);
lean_inc(v___x_2994_);
v___x_2995_ = l_Lean_Json_getNat_x3f(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2992_);
lean_dec(v_a_2980_);
lean_dec(v_val_2965_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
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
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3004_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_3005_ = lean_unsigned_to_nat(3u);
v___x_3006_ = lean_array_fget_borrowed(v_val_2965_, v___x_3005_);
lean_inc(v___x_3006_);
v___x_3007_ = l_Lean_Json_getNat_x3f(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec(v_a_3004_);
lean_dec(v_a_2992_);
lean_dec(v_a_2980_);
lean_dec(v_val_2965_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3007_, 1);
v___x_3017_ = lean_unsigned_to_nat(5u);
v___x_3018_ = lean_nat_dec_eq(v___x_2966_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_dec(v_val_2965_);
v___x_3019_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v___x_3019_);
lean_ctor_set(v___x_2890_, 3, v_a_3016_);
lean_ctor_set(v___x_2890_, 2, v_a_3004_);
lean_ctor_set(v___x_2890_, 1, v_a_2992_);
lean_ctor_set(v___x_2890_, 0, v_a_2980_);
v___x_3021_ = v___x_2890_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_2980_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_a_2992_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_a_3004_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_a_3016_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
v_a_2946_ = v___x_3021_;
goto v___jp_2945_;
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_array_fget(v_val_2965_, v___x_2967_);
lean_dec(v_val_2965_);
v___x_3024_ = l_Lean_Json_getStr_x3f(v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_a_3016_);
lean_dec(v_a_3004_);
lean_dec(v_a_2992_);
lean_dec(v_a_2980_);
lean_dec(v_a_2916_);
lean_del_object(v___x_2895_);
lean_dec(v_a_2893_);
lean_del_object(v___x_2890_);
lean_dec(v_r_2888_);
lean_dec(v_v_2886_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3024_, 1);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_a_3033_);
lean_ctor_set(v___x_2890_, 3, v_a_3016_);
lean_ctor_set(v___x_2890_, 2, v_a_3004_);
lean_ctor_set(v___x_2890_, 1, v_a_2992_);
lean_ctor_set(v___x_2890_, 0, v_a_2980_);
v___x_3035_ = v___x_2890_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_2980_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_2992_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_a_3004_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_a_3016_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_a_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v_a_2946_ = v___x_3035_;
goto v___jp_2945_;
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
v___jp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2920_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2886_, v___x_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_definition_x3f_2918_);
lean_dec(v_a_2916_);
lean_dec(v_a_2893_);
lean_dec(v_r_2888_);
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2920_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_a_2929_; size_t v_sz_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v_a_2929_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2920_, 1);
v_sz_2930_ = lean_array_size(v_a_2929_);
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2930_, v___x_2931_, v_a_2929_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_definition_x3f_2918_);
lean_dec(v_a_2916_);
lean_dec(v_a_2893_);
lean_dec(v_r_2888_);
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
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v_definition_x3f_2918_);
lean_ctor_set(v___x_2942_, 1, v_a_2941_);
v___x_2943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2916_, v___x_2942_, v_a_2893_);
v_init_2883_ = v___x_2943_;
v_x_2884_ = v_r_2888_;
goto _start;
}
}
}
v___jp_2945_:
{
lean_object* v___x_2948_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v_a_2946_);
v___x_2948_ = v___x_2895_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
v_definition_x3f_2918_ = v___x_2948_;
goto v___jp_2917_;
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
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_init_2883_);
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3051_, lean_object* v_k_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = l_Lean_Json_getObjValD(v_j_3051_, v_k_3052_);
v___x_3054_ = l_Lean_Json_getObj_x3f(v___x_3053_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_a_3063_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3054_, 1);
v___x_3064_ = lean_box(1);
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3064_, v_a_3063_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3066_, lean_object* v_k_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3066_, v_k_3067_);
lean_dec_ref(v_k_3067_);
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 1;
v___x_3075_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3078_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3079_ = lean_string_append(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3082_ = lean_string_append(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3085_ = lean_string_append(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = 1;
v___x_3090_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3093_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3094_ = lean_string_append(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3096_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3097_ = lean_string_append(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = 1;
v___x_3102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3102_, v___x_3101_);
return v___x_3103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3106_ = lean_string_append(v___x_3105_, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3109_ = lean_string_append(v___x_3108_, v___x_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3110_);
v___x_3112_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3110_, v___x_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_json_3110_);
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3122_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3122_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3117_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3118_ = lean_string_append(v___x_3117_, v_a_3113_);
lean_dec(v_a_3113_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3118_);
v___x_3120_ = v___x_3115_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_json_3110_);
v_a_3123_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3112_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3112_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 0);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_a_3131_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3110_);
v___x_3133_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3110_, v___x_3132_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3131_);
lean_dec(v_json_3110_);
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3143_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3143_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3139_ = lean_string_append(v___x_3138_, v_a_3134_);
lean_dec(v_a_3134_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3139_);
v___x_3141_ = v___x_3136_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
else
{
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3131_);
lean_dec(v_json_3110_);
v_a_3144_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3133_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3133_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 0);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_a_3152_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3153_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3110_, v___x_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_a_3152_);
lean_dec(v_a_3131_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3164_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3160_ = lean_string_append(v___x_3159_, v_a_3155_);
lean_dec(v_a_3155_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 0, v___x_3160_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
else
{
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v_a_3152_);
lean_dec(v_a_3131_);
v_a_3165_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3154_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3154_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set_tag(v___x_3167_, 0);
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3181_; 
v_a_3173_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3175_ = v___x_3154_;
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3154_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3177_, 0, v_a_3131_);
lean_ctor_set(v___x_3177_, 1, v_a_3152_);
lean_ctor_set(v___x_3177_, 2, v_a_3173_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3182_, lean_object* v_k_3183_, lean_object* v_v_3184_, lean_object* v_t_3185_, lean_object* v_hl_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3183_, v_v_3184_, v_t_3185_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3188_, lean_object* v_k_3189_, lean_object* v_v_3190_, lean_object* v_t_3191_, lean_object* v_hl_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3189_, v_v_3190_, v_t_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3196_, lean_object* v_x_3197_){
_start:
{
if (lean_obj_tag(v_x_3197_) == 0)
{
lean_object* v_k_3198_; lean_object* v_v_3199_; lean_object* v_l_3200_; lean_object* v_r_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_k_3198_ = lean_ctor_get(v_x_3197_, 1);
v_v_3199_ = lean_ctor_get(v_x_3197_, 2);
v_l_3200_ = lean_ctor_get(v_x_3197_, 3);
v_r_3201_ = lean_ctor_get(v_x_3197_, 4);
v___x_3202_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3196_, v_r_3201_);
lean_inc(v_v_3199_);
lean_inc(v_k_3198_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_k_3198_);
lean_ctor_set(v___x_3203_, 1, v_v_3199_);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
v_init_3196_ = v___x_3204_;
v_x_3197_ = v_l_3200_;
goto _start;
}
else
{
return v_init_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3206_, v_x_3207_);
lean_dec(v_x_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3209_, size_t v_i_3210_, lean_object* v_bs_3211_){
_start:
{
uint8_t v___x_3212_; 
v___x_3212_ = lean_usize_dec_lt(v_i_3210_, v_sz_3209_);
if (v___x_3212_ == 0)
{
return v_bs_3211_;
}
else
{
lean_object* v_v_3213_; lean_object* v___x_3214_; lean_object* v_bs_x27_3215_; size_t v___x_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v_v_3213_ = lean_array_uget(v_bs_3211_, v_i_3210_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v_bs_x27_3215_ = lean_array_uset(v_bs_3211_, v_i_3210_, v___x_3214_);
v___x_3216_ = ((size_t)1ULL);
v___x_3217_ = lean_usize_add(v_i_3210_, v___x_3216_);
v___x_3218_ = lean_array_uset(v_bs_x27_3215_, v_i_3210_, v_v_3213_);
v_i_3210_ = v___x_3217_;
v_bs_3211_ = v___x_3218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3220_, lean_object* v_i_3221_, lean_object* v_bs_3222_){
_start:
{
size_t v_sz_boxed_3223_; size_t v_i_boxed_3224_; lean_object* v_res_3225_; 
v_sz_boxed_3223_ = lean_unbox_usize(v_sz_3220_);
lean_dec(v_sz_3220_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_res_3225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3223_, v_i_boxed_3224_, v_bs_3222_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3226_){
_start:
{
size_t v_sz_3227_; size_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_sz_3227_ = lean_array_size(v_a_3226_);
v___x_3228_ = ((size_t)0ULL);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3227_, v___x_3228_, v_a_3226_);
v___x_3230_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = lean_array_mk(v_a_3231_);
v___x_3233_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3234_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_box(0);
return v___x_3235_;
}
else
{
lean_object* v_val_3236_; lean_object* v___x_3237_; 
v_val_3236_ = lean_ctor_get(v_x_3234_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v_x_3234_, 1);
v___x_3237_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3236_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
if (lean_obj_tag(v_a_3238_) == 0)
{
lean_object* v___x_3240_; 
v___x_3240_ = l_List_reverse___redArg(v_a_3239_);
return v___x_3240_;
}
else
{
lean_object* v_head_3241_; lean_object* v_tail_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3252_; 
v_head_3241_ = lean_ctor_get(v_a_3238_, 0);
v_tail_3242_ = lean_ctor_get(v_a_3238_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_a_3238_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3244_ = v_a_3238_;
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_tail_3242_);
lean_inc(v_head_3241_);
lean_dec(v_a_3238_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3252_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3246_ = l_Lean_JsonNumber_fromNat(v_head_3241_);
v___x_3247_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v_a_3239_);
lean_ctor_set(v___x_3244_, 0, v___x_3247_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_a_3239_);
v___x_3249_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
v_a_3238_ = v_tail_3242_;
v_a_3239_ = v___x_3249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3253_, size_t v_i_3254_, lean_object* v_bs_3255_){
_start:
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_usize_dec_lt(v_i_3254_, v_sz_3253_);
if (v___x_3256_ == 0)
{
return v_bs_3255_;
}
else
{
lean_object* v_v_3257_; lean_object* v_startPosLine_3258_; lean_object* v_startPosCharacter_3259_; lean_object* v_endPosLine_3260_; lean_object* v_endPosCharacter_3261_; lean_object* v___x_3262_; lean_object* v_bs_x27_3263_; lean_object* v___y_3265_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_range_3275_; lean_object* v___x_3276_; 
v_v_3257_ = lean_array_uget(v_bs_3255_, v_i_3254_);
v_startPosLine_3258_ = lean_ctor_get(v_v_3257_, 0);
v_startPosCharacter_3259_ = lean_ctor_get(v_v_3257_, 1);
v_endPosLine_3260_ = lean_ctor_get(v_v_3257_, 2);
v_endPosCharacter_3261_ = lean_ctor_get(v_v_3257_, 3);
v___x_3262_ = lean_unsigned_to_nat(0u);
v_bs_x27_3263_ = lean_array_uset(v_bs_3255_, v_i_3254_, v___x_3262_);
v___x_3270_ = lean_box(0);
lean_inc(v_endPosCharacter_3261_);
v___x_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_endPosCharacter_3261_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
lean_inc(v_endPosLine_3260_);
v___x_3272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_endPosLine_3260_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
lean_inc(v_startPosCharacter_3259_);
v___x_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_startPosCharacter_3259_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
lean_inc(v_startPosLine_3258_);
v___x_3274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3274_, 0, v_startPosLine_3258_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v_range_3275_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3274_, v___x_3270_);
v___x_3276_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3257_);
lean_dec(v_v_3257_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = l_List_appendTR___redArg(v_range_3275_, v___x_3270_);
v___y_3265_ = v___x_3277_;
goto v___jp_3264_;
}
else
{
lean_object* v_val_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3287_; 
v_val_3278_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3280_ = v___x_3276_;
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_val_3278_);
lean_dec(v___x_3276_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 3);
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_val_3278_);
v___x_3283_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___x_3270_);
v___x_3285_ = l_List_appendTR___redArg(v_range_3275_, v___x_3284_);
v___y_3265_ = v___x_3285_;
goto v___jp_3264_;
}
}
}
v___jp_3264_:
{
size_t v___x_3266_; size_t v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = ((size_t)1ULL);
v___x_3267_ = lean_usize_add(v_i_3254_, v___x_3266_);
v___x_3268_ = lean_array_uset(v_bs_x27_3263_, v_i_3254_, v___y_3265_);
v_i_3254_ = v___x_3267_;
v_bs_3255_ = v___x_3268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3288_, lean_object* v_i_3289_, lean_object* v_bs_3290_){
_start:
{
size_t v_sz_boxed_3291_; size_t v_i_boxed_3292_; lean_object* v_res_3293_; 
v_sz_boxed_3291_ = lean_unbox_usize(v_sz_3288_);
lean_dec(v_sz_3288_);
v_i_boxed_3292_ = lean_unbox_usize(v_i_3289_);
lean_dec(v_i_3289_);
v_res_3293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3291_, v_i_boxed_3292_, v_bs_3290_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3294_, size_t v_i_3295_, lean_object* v_bs_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_usize_dec_lt(v_i_3295_, v_sz_3294_);
if (v___x_3297_ == 0)
{
return v_bs_3296_;
}
else
{
lean_object* v_v_3298_; lean_object* v___x_3299_; lean_object* v_bs_x27_3300_; lean_object* v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; lean_object* v___x_3304_; 
v_v_3298_ = lean_array_uget(v_bs_3296_, v_i_3295_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v_bs_x27_3300_ = lean_array_uset(v_bs_3296_, v_i_3295_, v___x_3299_);
v___x_3301_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3298_);
v___x_3302_ = ((size_t)1ULL);
v___x_3303_ = lean_usize_add(v_i_3295_, v___x_3302_);
v___x_3304_ = lean_array_uset(v_bs_x27_3300_, v_i_3295_, v___x_3301_);
v_i_3295_ = v___x_3303_;
v_bs_3296_ = v___x_3304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3306_, lean_object* v_i_3307_, lean_object* v_bs_3308_){
_start:
{
size_t v_sz_boxed_3309_; size_t v_i_boxed_3310_; lean_object* v_res_3311_; 
v_sz_boxed_3309_ = lean_unbox_usize(v_sz_3306_);
lean_dec(v_sz_3306_);
v_i_boxed_3310_ = lean_unbox_usize(v_i_3307_);
lean_dec(v_i_3307_);
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3309_, v_i_boxed_3310_, v_bs_3308_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3312_){
_start:
{
size_t v_sz_3313_; size_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_sz_3313_ = lean_array_size(v_a_3312_);
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3313_, v___x_3314_, v_a_3312_);
v___x_3316_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
if (lean_obj_tag(v_a_3317_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = l_List_reverse___redArg(v_a_3318_);
return v___x_3319_;
}
else
{
lean_object* v_head_3320_; lean_object* v_snd_3321_; lean_object* v_tail_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3391_; 
v_head_3320_ = lean_ctor_get(v_a_3317_, 0);
lean_inc(v_head_3320_);
v_snd_3321_ = lean_ctor_get(v_head_3320_, 1);
lean_inc(v_snd_3321_);
v_tail_3322_ = lean_ctor_get(v_a_3317_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_a_3317_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; 
v_unused_3392_ = lean_ctor_get(v_a_3317_, 0);
lean_dec(v_unused_3392_);
v___x_3324_ = v_a_3317_;
v_isShared_3325_ = v_isSharedCheck_3391_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_tail_3322_);
lean_dec(v_a_3317_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3391_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_fst_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3389_; 
v_fst_3326_ = lean_ctor_get(v_head_3320_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_head_3320_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v_head_3320_, 1);
lean_dec(v_unused_3390_);
v___x_3328_ = v_head_3320_;
v_isShared_3329_ = v_isSharedCheck_3389_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_fst_3326_);
lean_dec(v_head_3320_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3389_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_definition_x3f_3330_; lean_object* v_usages_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3388_; 
v_definition_x3f_3330_ = lean_ctor_get(v_snd_3321_, 0);
v_usages_3331_ = lean_ctor_get(v_snd_3321_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_snd_3321_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3333_ = v_snd_3321_;
v_isShared_3334_ = v_isSharedCheck_3388_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_usages_3331_);
lean_inc(v_definition_x3f_3330_);
lean_dec(v_snd_3321_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3388_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___y_3339_; lean_object* v___y_3362_; 
v___x_3335_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3326_);
v___x_3336_ = l_Lean_Json_compress(v___x_3335_);
v___x_3337_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3330_) == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_box(0);
v___y_3339_ = v___x_3364_;
goto v___jp_3338_;
}
else
{
lean_object* v_val_3365_; lean_object* v_startPosLine_3366_; lean_object* v_startPosCharacter_3367_; lean_object* v_endPosLine_3368_; lean_object* v_endPosCharacter_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v_range_3375_; lean_object* v___x_3376_; 
v_val_3365_ = lean_ctor_get(v_definition_x3f_3330_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_definition_x3f_3330_, 1);
v_startPosLine_3366_ = lean_ctor_get(v_val_3365_, 0);
v_startPosCharacter_3367_ = lean_ctor_get(v_val_3365_, 1);
v_endPosLine_3368_ = lean_ctor_get(v_val_3365_, 2);
v_endPosCharacter_3369_ = lean_ctor_get(v_val_3365_, 3);
v___x_3370_ = lean_box(0);
lean_inc(v_endPosCharacter_3369_);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_endPosCharacter_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
lean_inc(v_endPosLine_3368_);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_endPosLine_3368_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
lean_inc(v_startPosCharacter_3367_);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_startPosCharacter_3367_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
lean_inc(v_startPosLine_3366_);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_startPosLine_3366_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v_range_3375_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3374_, v___x_3370_);
v___x_3376_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3365_);
lean_dec(v_val_3365_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = l_List_appendTR___redArg(v_range_3375_, v___x_3370_);
v___y_3362_ = v___x_3377_;
goto v___jp_3361_;
}
else
{
lean_object* v_val_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3387_; 
v_val_3378_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3380_ = v___x_3376_;
v_isShared_3381_ = v_isSharedCheck_3387_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_val_3378_);
lean_dec(v___x_3376_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3387_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set_tag(v___x_3380_, 3);
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_val_3378_);
v___x_3383_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___x_3370_);
v___x_3385_ = l_List_appendTR___redArg(v_range_3375_, v___x_3384_);
v___y_3362_ = v___x_3385_;
goto v___jp_3361_;
}
}
}
}
v___jp_3338_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3339_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3340_);
lean_ctor_set(v___x_3328_, 0, v___x_3337_);
v___x_3342_ = v___x_3328_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; size_t v_sz_3344_; size_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3343_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3344_ = lean_array_size(v_usages_3331_);
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3344_, v___x_3345_, v_usages_3331_);
v___x_3347_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3346_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 1, v___x_3347_);
lean_ctor_set(v___x_3333_, 0, v___x_3343_);
v___x_3349_ = v___x_3333_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3350_ = lean_box(0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v___x_3350_);
lean_ctor_set(v___x_3324_, 0, v___x_3349_);
v___x_3352_ = v___x_3324_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3342_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_Json_mkObj(v___x_3353_);
lean_dec_ref_known(v___x_3353_, 2);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3336_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v_a_3318_);
v_a_3317_ = v_tail_3322_;
v_a_3318_ = v___x_3356_;
goto _start;
}
}
}
}
v___jp_3361_:
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___y_3362_);
v___y_3339_ = v___x_3363_;
goto v___jp_3338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
if (lean_obj_tag(v_a_3393_) == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = l_List_reverse___redArg(v_a_3394_);
return v___x_3395_;
}
else
{
lean_object* v_head_3396_; lean_object* v_snd_3397_; lean_object* v_tail_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3450_; 
v_head_3396_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_head_3396_);
v_snd_3397_ = lean_ctor_get(v_head_3396_, 1);
lean_inc(v_snd_3397_);
v_tail_3398_ = lean_ctor_get(v_a_3393_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_a_3393_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v_a_3393_, 0);
lean_dec(v_unused_3451_);
v___x_3400_ = v_a_3393_;
v_isShared_3401_ = v_isSharedCheck_3450_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_tail_3398_);
lean_dec(v_a_3393_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3450_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_fst_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3448_; 
v_fst_3402_ = lean_ctor_get(v_head_3396_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_head_3396_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v_head_3396_, 1);
lean_dec(v_unused_3449_);
v___x_3404_ = v_head_3396_;
v_isShared_3405_ = v_isSharedCheck_3448_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_fst_3402_);
lean_dec(v_head_3396_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3448_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_rangeStartPosLine_3406_; lean_object* v_rangeStartPosCharacter_3407_; lean_object* v_rangeEndPosLine_3408_; lean_object* v_rangeEndPosCharacter_3409_; lean_object* v_selectionRangeStartPosLine_3410_; lean_object* v_selectionRangeStartPosCharacter_3411_; lean_object* v_selectionRangeEndPosLine_3412_; lean_object* v_selectionRangeEndPosCharacter_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v_rangeStartPosLine_3406_ = lean_ctor_get(v_snd_3397_, 0);
lean_inc(v_rangeStartPosLine_3406_);
v_rangeStartPosCharacter_3407_ = lean_ctor_get(v_snd_3397_, 1);
lean_inc(v_rangeStartPosCharacter_3407_);
v_rangeEndPosLine_3408_ = lean_ctor_get(v_snd_3397_, 2);
lean_inc(v_rangeEndPosLine_3408_);
v_rangeEndPosCharacter_3409_ = lean_ctor_get(v_snd_3397_, 3);
lean_inc(v_rangeEndPosCharacter_3409_);
v_selectionRangeStartPosLine_3410_ = lean_ctor_get(v_snd_3397_, 4);
lean_inc(v_selectionRangeStartPosLine_3410_);
v_selectionRangeStartPosCharacter_3411_ = lean_ctor_get(v_snd_3397_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3411_);
v_selectionRangeEndPosLine_3412_ = lean_ctor_get(v_snd_3397_, 6);
lean_inc(v_selectionRangeEndPosLine_3412_);
v_selectionRangeEndPosCharacter_3413_ = lean_ctor_get(v_snd_3397_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3413_);
lean_dec(v_snd_3397_);
v___x_3414_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3406_);
v___x_3415_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
v___x_3416_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3407_);
v___x_3417_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
v___x_3418_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3408_);
v___x_3419_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
v___x_3420_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3409_);
v___x_3421_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
v___x_3422_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3410_);
v___x_3423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
v___x_3424_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3411_);
v___x_3425_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
v___x_3426_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3412_);
v___x_3427_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
v___x_3428_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3413_);
v___x_3429_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
v___x_3430_ = lean_unsigned_to_nat(8u);
v___x_3431_ = lean_mk_empty_array_with_capacity(v___x_3430_);
v___x_3432_ = lean_array_push(v___x_3431_, v___x_3415_);
v___x_3433_ = lean_array_push(v___x_3432_, v___x_3417_);
v___x_3434_ = lean_array_push(v___x_3433_, v___x_3419_);
v___x_3435_ = lean_array_push(v___x_3434_, v___x_3421_);
v___x_3436_ = lean_array_push(v___x_3435_, v___x_3423_);
v___x_3437_ = lean_array_push(v___x_3436_, v___x_3425_);
v___x_3438_ = lean_array_push(v___x_3437_, v___x_3427_);
v___x_3439_ = lean_array_push(v___x_3438_, v___x_3429_);
v___x_3440_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3440_);
v___x_3442_ = v___x_3404_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_fst_3402_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v_a_3394_);
lean_ctor_set(v___x_3400_, 0, v___x_3442_);
v___x_3444_ = v___x_3400_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_a_3394_);
v___x_3444_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3393_ = v_tail_3398_;
v_a_3394_ = v___x_3444_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3452_, lean_object* v_x_3453_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 0)
{
lean_object* v_k_3454_; lean_object* v_v_3455_; lean_object* v_l_3456_; lean_object* v_r_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_k_3454_ = lean_ctor_get(v_x_3453_, 1);
v_v_3455_ = lean_ctor_get(v_x_3453_, 2);
v_l_3456_ = lean_ctor_get(v_x_3453_, 3);
v_r_3457_ = lean_ctor_get(v_x_3453_, 4);
v___x_3458_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3452_, v_r_3457_);
lean_inc(v_v_3455_);
lean_inc(v_k_3454_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_k_3454_);
lean_ctor_set(v___x_3459_, 1, v_v_3455_);
v___x_3460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___x_3458_);
v_init_3452_ = v___x_3460_;
v_x_3453_ = v_l_3456_;
goto _start;
}
else
{
return v_init_3452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3462_, lean_object* v_x_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3462_, v_x_3463_);
lean_dec(v_x_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3465_){
_start:
{
lean_object* v_version_3466_; lean_object* v_references_3467_; lean_object* v_decls_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_version_3466_ = lean_ctor_get(v_x_3465_, 0);
lean_inc(v_version_3466_);
v_references_3467_ = lean_ctor_get(v_x_3465_, 1);
lean_inc(v_references_3467_);
v_decls_3468_ = lean_ctor_get(v_x_3465_, 2);
lean_inc(v_decls_3468_);
lean_dec_ref(v_x_3465_);
v___x_3469_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3470_ = l_Lean_JsonNumber_fromNat(v_version_3466_);
v___x_3471_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3469_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3476_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3473_, v_references_3467_);
lean_dec(v_references_3467_);
v___x_3477_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3476_, v___x_3473_);
v___x_3478_ = l_Lean_Json_mkObj(v___x_3477_);
lean_dec(v___x_3477_);
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3475_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v___x_3473_);
v___x_3481_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3482_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3473_, v_decls_3468_);
lean_dec(v_decls_3468_);
v___x_3483_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3482_, v___x_3473_);
v___x_3484_ = l_Lean_Json_mkObj(v___x_3483_);
lean_dec(v___x_3483_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3481_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___x_3473_);
v___x_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v___x_3473_);
v___x_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3480_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3474_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3491_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3489_, v___x_3490_);
v___x_3492_ = l_Lean_Json_mkObj(v___x_3491_);
lean_dec(v___x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3495_, size_t v_i_3496_, lean_object* v_bs_3497_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_lt(v_i_3496_, v_sz_3495_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_bs_3497_);
return v___x_3499_;
}
else
{
lean_object* v_v_3500_; lean_object* v___x_3501_; 
v_v_3500_ = lean_array_uget_borrowed(v_bs_3497_, v_i_3496_);
lean_inc(v_v_3500_);
v___x_3501_ = l_Lean_Json_getStr_x3f(v_v_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_bs_3497_);
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v_bs_x27_3512_; size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
v_a_3510_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3511_ = lean_unsigned_to_nat(0u);
v_bs_x27_3512_ = lean_array_uset(v_bs_3497_, v_i_3496_, v___x_3511_);
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3496_, v___x_3513_);
v___x_3515_ = lean_array_uset(v_bs_x27_3512_, v_i_3496_, v_a_3510_);
v_i_3496_ = v___x_3514_;
v_bs_3497_ = v___x_3515_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3517_, lean_object* v_i_3518_, lean_object* v_bs_3519_){
_start:
{
size_t v_sz_boxed_3520_; size_t v_i_boxed_3521_; lean_object* v_res_3522_; 
v_sz_boxed_3520_ = lean_unbox_usize(v_sz_3517_);
lean_dec(v_sz_3517_);
v_i_boxed_3521_ = lean_unbox_usize(v_i_3518_);
lean_dec(v_i_3518_);
v_res_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3520_, v_i_boxed_3521_, v_bs_3519_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3523_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 4)
{
lean_object* v_elems_3524_; size_t v_sz_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
v_elems_3524_ = lean_ctor_get(v_x_3523_, 0);
lean_inc_ref(v_elems_3524_);
lean_dec_ref_known(v_x_3523_, 1);
v_sz_3525_ = lean_array_size(v_elems_3524_);
v___x_3526_ = ((size_t)0ULL);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3525_, v___x_3526_, v_elems_3524_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3528_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3529_ = lean_unsigned_to_nat(80u);
v___x_3530_ = l_Lean_Json_pretty(v_x_3523_, v___x_3529_);
v___x_3531_ = lean_string_append(v___x_3528_, v___x_3530_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3533_ = lean_string_append(v___x_3531_, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3535_, lean_object* v_k_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = l_Lean_Json_getObjValD(v_j_3535_, v_k_3536_);
v___x_3538_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3539_, lean_object* v_k_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3539_, v_k_3540_);
lean_dec_ref(v_k_3540_);
return v_res_3541_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = 1;
v___x_3549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3549_, v___x_3548_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3553_ = lean_string_append(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = 1;
v___x_3557_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3560_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3561_ = lean_string_append(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3564_ = lean_string_append(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3565_){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3567_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3565_, v___x_3566_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3577_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3573_ = lean_string_append(v___x_3572_, v_a_3568_);
lean_dec(v_a_3568_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3573_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
v_a_3578_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3567_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3567_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 0);
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v_a_3586_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3567_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3567_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3596_, size_t v_i_3597_, lean_object* v_bs_3598_){
_start:
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_usize_dec_lt(v_i_3597_, v_sz_3596_);
if (v___x_3599_ == 0)
{
return v_bs_3598_;
}
else
{
lean_object* v_v_3600_; lean_object* v___x_3601_; lean_object* v_bs_x27_3602_; lean_object* v___x_3603_; size_t v___x_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_v_3600_ = lean_array_uget(v_bs_3598_, v_i_3597_);
v___x_3601_ = lean_unsigned_to_nat(0u);
v_bs_x27_3602_ = lean_array_uset(v_bs_3598_, v_i_3597_, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_v_3600_);
v___x_3604_ = ((size_t)1ULL);
v___x_3605_ = lean_usize_add(v_i_3597_, v___x_3604_);
v___x_3606_ = lean_array_uset(v_bs_x27_3602_, v_i_3597_, v___x_3603_);
v_i_3597_ = v___x_3605_;
v_bs_3598_ = v___x_3606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3608_, lean_object* v_i_3609_, lean_object* v_bs_3610_){
_start:
{
size_t v_sz_boxed_3611_; size_t v_i_boxed_3612_; lean_object* v_res_3613_; 
v_sz_boxed_3611_ = lean_unbox_usize(v_sz_3608_);
lean_dec(v_sz_3608_);
v_i_boxed_3612_ = lean_unbox_usize(v_i_3609_);
lean_dec(v_i_3609_);
v_res_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3611_, v_i_boxed_3612_, v_bs_3610_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3614_){
_start:
{
size_t v_sz_3615_; size_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_sz_3615_ = lean_array_size(v_a_3614_);
v___x_3616_ = ((size_t)0ULL);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3615_, v___x_3616_, v_a_3614_);
v___x_3618_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3619_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3620_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3621_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3619_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_box(0);
v___x_3624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v___x_3623_);
v___x_3626_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3627_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3625_, v___x_3626_);
v___x_3628_ = l_Lean_Json_mkObj(v___x_3627_);
lean_dec(v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3631_, lean_object* v_k_3632_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = l_Lean_Json_getObjValD(v_j_3631_, v_k_3632_);
v___x_3634_ = l_Lean_Json_getStr_x3f(v___x_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3635_, lean_object* v_k_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3635_, v_k_3636_);
lean_dec_ref(v_k_3636_);
return v_res_3637_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = 1;
v___x_3645_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3648_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3649_ = lean_string_append(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = 1;
v___x_3653_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3654_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3653_, v___x_3652_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3656_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3657_ = lean_string_append(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3659_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3660_ = lean_string_append(v___x_3659_, v___x_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3661_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3663_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3661_, v___x_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3673_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
v___x_3668_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3669_ = lean_string_append(v___x_3668_, v_a_3664_);
lean_dec(v_a_3664_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3669_);
v___x_3671_ = v___x_3666_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
v_a_3674_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3663_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3663_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3682_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3663_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3663_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3692_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3694_, 0, v_x_3692_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = lean_box(0);
v___x_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
v___x_3699_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3700_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3698_, v___x_3699_);
v___x_3701_ = l_Lean_Json_mkObj(v___x_3700_);
lean_dec(v___x_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3704_){
_start:
{
if (lean_obj_tag(v_x_3704_) == 0)
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
return v___x_3705_;
}
else
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_unsigned_to_nat(1u);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3707_);
lean_dec_ref(v_x_3707_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3709_, lean_object* v_k_3710_){
_start:
{
if (lean_obj_tag(v_t_3709_) == 0)
{
lean_object* v_namespace_3711_; lean_object* v_exceptions_3712_; lean_object* v___x_3713_; 
v_namespace_3711_ = lean_ctor_get(v_t_3709_, 0);
lean_inc(v_namespace_3711_);
v_exceptions_3712_ = lean_ctor_get(v_t_3709_, 1);
lean_inc_ref(v_exceptions_3712_);
lean_dec_ref_known(v_t_3709_, 2);
v___x_3713_ = lean_apply_2(v_k_3710_, v_namespace_3711_, v_exceptions_3712_);
return v___x_3713_;
}
else
{
lean_object* v_from_3714_; lean_object* v_to_3715_; lean_object* v___x_3716_; 
v_from_3714_ = lean_ctor_get(v_t_3709_, 0);
lean_inc(v_from_3714_);
v_to_3715_ = lean_ctor_get(v_t_3709_, 1);
lean_inc(v_to_3715_);
lean_dec_ref_known(v_t_3709_, 2);
v___x_3716_ = lean_apply_2(v_k_3710_, v_from_3714_, v_to_3715_);
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3717_, lean_object* v_ctorIdx_3718_, lean_object* v_t_3719_, lean_object* v_h_3720_, lean_object* v_k_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3719_, v_k_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3723_, lean_object* v_ctorIdx_3724_, lean_object* v_t_3725_, lean_object* v_h_3726_, lean_object* v_k_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3723_, v_ctorIdx_3724_, v_t_3725_, v_h_3726_, v_k_3727_);
lean_dec(v_ctorIdx_3724_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3729_, lean_object* v_allExcept_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3729_, v_allExcept_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3732_, lean_object* v_t_3733_, lean_object* v_h_3734_, lean_object* v_allExcept_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3733_, v_allExcept_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3737_, lean_object* v_renamed_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3737_, v_renamed_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3740_, lean_object* v_t_3741_, lean_object* v_h_3742_, lean_object* v_renamed_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3741_, v_renamed_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3745_, size_t v_i_3746_, lean_object* v_bs_3747_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3746_, v_sz_3745_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_bs_3747_);
return v___x_3749_;
}
else
{
lean_object* v_v_3750_; lean_object* v___x_3751_; 
v_v_3750_ = lean_array_uget_borrowed(v_bs_3747_, v_i_3746_);
lean_inc(v_v_3750_);
v___x_3751_ = l_Lean_Name_fromJson_x3f(v_v_3750_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v_bs_3747_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3761_; lean_object* v_bs_x27_3762_; size_t v___x_3763_; size_t v___x_3764_; lean_object* v___x_3765_; 
v_a_3760_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3761_ = lean_unsigned_to_nat(0u);
v_bs_x27_3762_ = lean_array_uset(v_bs_3747_, v_i_3746_, v___x_3761_);
v___x_3763_ = ((size_t)1ULL);
v___x_3764_ = lean_usize_add(v_i_3746_, v___x_3763_);
v___x_3765_ = lean_array_uset(v_bs_x27_3762_, v_i_3746_, v_a_3760_);
v_i_3746_ = v___x_3764_;
v_bs_3747_ = v___x_3765_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_bs_3769_){
_start:
{
size_t v_sz_boxed_3770_; size_t v_i_boxed_3771_; lean_object* v_res_3772_; 
v_sz_boxed_3770_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3771_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3770_, v_i_boxed_3771_, v_bs_3769_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3773_){
_start:
{
if (lean_obj_tag(v_x_3773_) == 4)
{
lean_object* v_elems_3774_; size_t v_sz_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v_elems_3774_ = lean_ctor_get(v_x_3773_, 0);
lean_inc_ref(v_elems_3774_);
lean_dec_ref_known(v_x_3773_, 1);
v_sz_3775_ = lean_array_size(v_elems_3774_);
v___x_3776_ = ((size_t)0ULL);
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3775_, v___x_3776_, v_elems_3774_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3778_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3779_ = lean_unsigned_to_nat(80u);
v___x_3780_ = l_Lean_Json_pretty(v_x_3773_, v___x_3779_);
v___x_3781_ = lean_string_append(v___x_3778_, v___x_3780_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3819_){
_start:
{
lean_object* v___x_3820_; 
lean_inc(v_json_3819_);
v___x_3820_ = l_Lean_Json_getTag_x3f(v_json_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v___x_3821_; 
lean_dec(v_json_3819_);
v___x_3821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_val_3822_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_val_3822_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3823_ = lean_box(0);
v___x_3824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3825_ = lean_string_dec_eq(v_val_3822_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3827_ = lean_string_dec_eq(v_val_3822_, v___x_3826_);
lean_dec(v_val_3822_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec(v_json_3819_);
v___x_3828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3828_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_unsigned_to_nat(2u);
v___x_3830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3831_ = l_Lean_Json_parseCtorFields(v_json_3819_, v___x_3826_, v___x_3829_, v___x_3830_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v_a_3840_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = lean_array_get_borrowed(v___x_3823_, v_a_3840_, v___x_3841_);
lean_inc(v___x_3842_);
v___x_3843_ = l_Lean_Name_fromJson_x3f(v___x_3842_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_a_3840_);
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3843_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3843_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_a_3852_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3843_, 1);
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = lean_array_get(v___x_3823_, v_a_3840_, v___x_3853_);
lean_dec(v_a_3840_);
v___x_3855_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3854_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec(v_a_3852_);
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
v_a_3864_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3866_ = v___x_3855_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3855_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v_a_3852_);
lean_ctor_set(v___x_3868_, 1, v_a_3864_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3868_);
v___x_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec(v_val_3822_);
v___x_3873_ = lean_unsigned_to_nat(2u);
v___x_3874_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3875_ = l_Lean_Json_parseCtorFields(v_json_3819_, v___x_3824_, v___x_3873_, v___x_3874_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_a_3884_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3875_, 1);
v___x_3885_ = lean_unsigned_to_nat(0u);
v___x_3886_ = lean_array_get_borrowed(v___x_3823_, v_a_3884_, v___x_3885_);
lean_inc(v___x_3886_);
v___x_3887_ = l_Lean_Name_fromJson_x3f(v___x_3886_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_a_3884_);
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3887_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_a_3896_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_array_get(v___x_3823_, v_a_3884_, v___x_3897_);
lean_dec(v_a_3884_);
v___x_3899_ = l_Lean_Name_fromJson_x3f(v___x_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v_a_3896_);
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3916_; 
v_a_3908_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3910_ = v___x_3899_;
v_isShared_3911_ = v_isSharedCheck_3916_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3899_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3916_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_a_3896_);
lean_ctor_set(v___x_3912_, 1, v_a_3908_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3912_);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3919_, size_t v_i_3920_, lean_object* v_bs_3921_){
_start:
{
uint8_t v___x_3922_; 
v___x_3922_ = lean_usize_dec_lt(v_i_3920_, v_sz_3919_);
if (v___x_3922_ == 0)
{
return v_bs_3921_;
}
else
{
lean_object* v_v_3923_; lean_object* v___x_3924_; lean_object* v_bs_x27_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
v_v_3923_ = lean_array_uget(v_bs_3921_, v_i_3920_);
v___x_3924_ = lean_unsigned_to_nat(0u);
v_bs_x27_3925_ = lean_array_uset(v_bs_3921_, v_i_3920_, v___x_3924_);
v___x_3926_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3923_, v___x_3922_);
v___x_3927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = lean_usize_add(v_i_3920_, v___x_3928_);
v___x_3930_ = lean_array_uset(v_bs_x27_3925_, v_i_3920_, v___x_3927_);
v_i_3920_ = v___x_3929_;
v_bs_3921_ = v___x_3930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_bs_3934_){
_start:
{
size_t v_sz_boxed_3935_; size_t v_i_boxed_3936_; lean_object* v_res_3937_; 
v_sz_boxed_3935_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3936_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3935_, v_i_boxed_3936_, v_bs_3934_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3938_){
_start:
{
size_t v_sz_3939_; size_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_sz_3939_ = lean_array_size(v_a_3938_);
v___x_3940_ = ((size_t)0ULL);
v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3939_, v___x_3940_, v_a_3938_);
v___x_3942_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3943_){
_start:
{
if (lean_obj_tag(v_x_3943_) == 0)
{
lean_object* v_namespace_3944_; lean_object* v_exceptions_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3967_; 
v_namespace_3944_ = lean_ctor_get(v_x_3943_, 0);
v_exceptions_3945_ = lean_ctor_get(v_x_3943_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_x_3943_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3947_ = v_x_3943_;
v_isShared_3948_ = v_isSharedCheck_3967_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_exceptions_3945_);
lean_inc(v_namespace_3944_);
lean_dec(v_x_3943_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3967_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3949_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3950_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3951_ = 1;
v___x_3952_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3944_, v___x_3951_);
v___x_3953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v___x_3953_);
lean_ctor_set(v___x_3947_, 0, v___x_3950_);
v___x_3955_ = v___x_3947_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3957_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3945_);
v___x_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3958_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3955_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_Json_mkObj(v___x_3961_);
lean_dec_ref_known(v___x_3961_, 2);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3949_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3959_);
v___x_3965_ = l_Lean_Json_mkObj(v___x_3964_);
lean_dec_ref_known(v___x_3964_, 2);
return v___x_3965_;
}
}
}
else
{
lean_object* v_from_3968_; lean_object* v_to_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3992_; 
v_from_3968_ = lean_ctor_get(v_x_3943_, 0);
v_to_3969_ = lean_ctor_get(v_x_3943_, 1);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_x_3943_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3971_ = v_x_3943_;
v_isShared_3972_ = v_isSharedCheck_3992_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_to_3969_);
lean_inc(v_from_3968_);
lean_dec(v_x_3943_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3992_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3975_ = 1;
v___x_3976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3968_, v___x_3975_);
v___x_3977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 0);
lean_ctor_set(v___x_3971_, 1, v___x_3977_);
lean_ctor_set(v___x_3971_, 0, v___x_3974_);
v___x_3979_ = v___x_3971_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3981_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3969_, v___x_3975_);
v___x_3982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3980_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_box(0);
v___x_3985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3979_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = l_Lean_Json_mkObj(v___x_3986_);
lean_dec_ref_known(v___x_3986_, 2);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3973_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v___x_3984_);
v___x_3990_ = l_Lean_Json_mkObj(v___x_3989_);
lean_dec_ref_known(v___x_3989_, 2);
return v___x_3990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3995_, size_t v_i_3996_, lean_object* v_bs_3997_){
_start:
{
uint8_t v___x_3998_; 
v___x_3998_ = lean_usize_dec_lt(v_i_3996_, v_sz_3995_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3999_, 0, v_bs_3997_);
return v___x_3999_;
}
else
{
lean_object* v_v_4000_; lean_object* v___x_4001_; 
v_v_4000_ = lean_array_uget_borrowed(v_bs_3997_, v_i_3996_);
lean_inc(v_v_4000_);
v___x_4001_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_4000_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_bs_3997_);
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4011_; lean_object* v_bs_x27_4012_; size_t v___x_4013_; size_t v___x_4014_; lean_object* v___x_4015_; 
v_a_4010_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4001_, 1);
v___x_4011_ = lean_unsigned_to_nat(0u);
v_bs_x27_4012_ = lean_array_uset(v_bs_3997_, v_i_3996_, v___x_4011_);
v___x_4013_ = ((size_t)1ULL);
v___x_4014_ = lean_usize_add(v_i_3996_, v___x_4013_);
v___x_4015_ = lean_array_uset(v_bs_x27_4012_, v_i_3996_, v_a_4010_);
v_i_3996_ = v___x_4014_;
v_bs_3997_ = v___x_4015_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4017_, lean_object* v_i_4018_, lean_object* v_bs_4019_){
_start:
{
size_t v_sz_boxed_4020_; size_t v_i_boxed_4021_; lean_object* v_res_4022_; 
v_sz_boxed_4020_ = lean_unbox_usize(v_sz_4017_);
lean_dec(v_sz_4017_);
v_i_boxed_4021_ = lean_unbox_usize(v_i_4018_);
lean_dec(v_i_4018_);
v_res_4022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4020_, v_i_boxed_4021_, v_bs_4019_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4023_){
_start:
{
if (lean_obj_tag(v_x_4023_) == 4)
{
lean_object* v_elems_4024_; size_t v_sz_4025_; size_t v___x_4026_; lean_object* v___x_4027_; 
v_elems_4024_ = lean_ctor_get(v_x_4023_, 0);
lean_inc_ref(v_elems_4024_);
lean_dec_ref_known(v_x_4023_, 1);
v_sz_4025_ = lean_array_size(v_elems_4024_);
v___x_4026_ = ((size_t)0ULL);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4025_, v___x_4026_, v_elems_4024_);
return v___x_4027_;
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4028_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4029_ = lean_unsigned_to_nat(80u);
v___x_4030_ = l_Lean_Json_pretty(v_x_4023_, v___x_4029_);
v___x_4031_ = lean_string_append(v___x_4028_, v___x_4030_);
lean_dec_ref(v___x_4030_);
v___x_4032_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4033_ = lean_string_append(v___x_4031_, v___x_4032_);
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4035_, lean_object* v_k_4036_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = l_Lean_Json_getObjValD(v_j_4035_, v_k_4036_);
v___x_4038_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4039_, lean_object* v_k_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4039_, v_k_4040_);
lean_dec_ref(v_k_4040_);
return v_res_4041_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = 1;
v___x_4049_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4050_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4049_, v___x_4048_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4052_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4053_ = lean_string_append(v___x_4052_, v___x_4051_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = 1;
v___x_4057_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4058_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4057_, v___x_4056_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4060_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4061_ = lean_string_append(v___x_4060_, v___x_4059_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4063_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4064_ = lean_string_append(v___x_4063_, v___x_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = 1;
v___x_4069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4070_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4069_, v___x_4068_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4071_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4072_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4073_ = lean_string_append(v___x_4072_, v___x_4071_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4076_ = lean_string_append(v___x_4075_, v___x_4074_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4077_){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4077_);
v___x_4079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4077_, v___x_4078_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_json_4077_);
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4089_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4085_ = lean_string_append(v___x_4084_, v_a_4080_);
lean_dec(v_a_4080_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4085_);
v___x_4087_ = v___x_4082_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
else
{
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_json_4077_);
v_a_4090_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4079_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4079_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
lean_ctor_set_tag(v___x_4092_, 0);
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_a_4098_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4077_, v___x_4099_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4098_);
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4106_ = lean_string_append(v___x_4105_, v_a_4101_);
lean_dec(v_a_4101_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4106_);
v___x_4108_ = v___x_4103_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
else
{
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v_a_4098_);
v_a_4111_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4100_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4100_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
lean_ctor_set_tag(v___x_4113_, 0);
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4127_; 
v_a_4119_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4121_ = v___x_4100_;
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4100_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4098_);
lean_ctor_set(v___x_4123_, 1, v_a_4119_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4123_);
v___x_4125_ = v___x_4121_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4130_, size_t v_i_4131_, lean_object* v_bs_4132_){
_start:
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_usize_dec_lt(v_i_4131_, v_sz_4130_);
if (v___x_4133_ == 0)
{
return v_bs_4132_;
}
else
{
lean_object* v_v_4134_; lean_object* v___x_4135_; lean_object* v_bs_x27_4136_; lean_object* v___x_4137_; size_t v___x_4138_; size_t v___x_4139_; lean_object* v___x_4140_; 
v_v_4134_ = lean_array_uget(v_bs_4132_, v_i_4131_);
v___x_4135_ = lean_unsigned_to_nat(0u);
v_bs_x27_4136_ = lean_array_uset(v_bs_4132_, v_i_4131_, v___x_4135_);
v___x_4137_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4134_);
v___x_4138_ = ((size_t)1ULL);
v___x_4139_ = lean_usize_add(v_i_4131_, v___x_4138_);
v___x_4140_ = lean_array_uset(v_bs_x27_4136_, v_i_4131_, v___x_4137_);
v_i_4131_ = v___x_4139_;
v_bs_4132_ = v___x_4140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4142_, lean_object* v_i_4143_, lean_object* v_bs_4144_){
_start:
{
size_t v_sz_boxed_4145_; size_t v_i_boxed_4146_; lean_object* v_res_4147_; 
v_sz_boxed_4145_ = lean_unbox_usize(v_sz_4142_);
lean_dec(v_sz_4142_);
v_i_boxed_4146_ = lean_unbox_usize(v_i_4143_);
lean_dec(v_i_4143_);
v_res_4147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4145_, v_i_boxed_4146_, v_bs_4144_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4148_){
_start:
{
size_t v_sz_4149_; size_t v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_sz_4149_ = lean_array_size(v_a_4148_);
v___x_4150_ = ((size_t)0ULL);
v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4149_, v___x_4150_, v_a_4148_);
v___x_4152_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4153_){
_start:
{
lean_object* v_identifier_4154_; lean_object* v_openNamespaces_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4175_; 
v_identifier_4154_ = lean_ctor_get(v_x_4153_, 0);
v_openNamespaces_4155_ = lean_ctor_get(v_x_4153_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_x_4153_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4157_ = v_x_4153_;
v_isShared_4158_ = v_isSharedCheck_4175_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_openNamespaces_4155_);
lean_inc(v_identifier_4154_);
lean_dec(v_x_4153_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4175_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4159_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_identifier_4154_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4160_);
lean_ctor_set(v___x_4157_, 0, v___x_4159_);
v___x_4162_ = v___x_4157_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4163_ = lean_box(0);
v___x_4164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4166_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4155_);
v___x_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v___x_4163_);
v___x_4169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v___x_4163_);
v___x_4170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4164_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4172_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4170_, v___x_4171_);
v___x_4173_ = l_Lean_Json_mkObj(v___x_4172_);
lean_dec(v___x_4172_);
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4181_, lean_object* v_k_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_Json_getObjValD(v_j_4181_, v_k_4182_);
switch(lean_obj_tag(v___x_4183_))
{
case 3:
{
lean_object* v_s_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4192_; 
v_s_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_s_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
lean_ctor_set_tag(v___x_4186_, 0);
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_s_4184_);
v___x_4189_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; 
v___x_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
}
case 2:
{
lean_object* v_n_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4201_; 
v_n_4193_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4195_ = v___x_4183_;
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_n_4193_);
lean_dec(v___x_4183_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4201_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 1);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_n_4193_);
v___x_4198_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
}
}
default: 
{
lean_object* v___x_4202_; 
lean_dec(v___x_4183_);
v___x_4202_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4203_, lean_object* v_k_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4203_, v_k_4204_);
lean_dec_ref(v_k_4204_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4206_, size_t v_i_4207_, lean_object* v_bs_4208_){
_start:
{
uint8_t v___x_4209_; 
v___x_4209_ = lean_usize_dec_lt(v_i_4207_, v_sz_4206_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_bs_4208_);
return v___x_4210_;
}
else
{
lean_object* v_v_4211_; lean_object* v___x_4212_; 
v_v_4211_ = lean_array_uget_borrowed(v_bs_4208_, v_i_4207_);
lean_inc(v_v_4211_);
v___x_4212_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4211_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v_bs_4208_);
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4222_; lean_object* v_bs_x27_4223_; size_t v___x_4224_; size_t v___x_4225_; lean_object* v___x_4226_; 
v_a_4221_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4222_ = lean_unsigned_to_nat(0u);
v_bs_x27_4223_ = lean_array_uset(v_bs_4208_, v_i_4207_, v___x_4222_);
v___x_4224_ = ((size_t)1ULL);
v___x_4225_ = lean_usize_add(v_i_4207_, v___x_4224_);
v___x_4226_ = lean_array_uset(v_bs_x27_4223_, v_i_4207_, v_a_4221_);
v_i_4207_ = v___x_4225_;
v_bs_4208_ = v___x_4226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4228_, lean_object* v_i_4229_, lean_object* v_bs_4230_){
_start:
{
size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4228_);
lean_dec(v_sz_4228_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4229_);
lean_dec(v_i_4229_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4231_, v_i_boxed_4232_, v_bs_4230_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4234_){
_start:
{
if (lean_obj_tag(v_x_4234_) == 4)
{
lean_object* v_elems_4235_; size_t v_sz_4236_; size_t v___x_4237_; lean_object* v___x_4238_; 
v_elems_4235_ = lean_ctor_get(v_x_4234_, 0);
lean_inc_ref(v_elems_4235_);
lean_dec_ref_known(v_x_4234_, 1);
v_sz_4236_ = lean_array_size(v_elems_4235_);
v___x_4237_ = ((size_t)0ULL);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4236_, v___x_4237_, v_elems_4235_);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4239_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4240_ = lean_unsigned_to_nat(80u);
v___x_4241_ = l_Lean_Json_pretty(v_x_4234_, v___x_4240_);
v___x_4242_ = lean_string_append(v___x_4239_, v___x_4241_);
lean_dec_ref(v___x_4241_);
v___x_4243_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4244_ = lean_string_append(v___x_4242_, v___x_4243_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
return v___x_4245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4246_, lean_object* v_k_4247_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = l_Lean_Json_getObjValD(v_j_4246_, v_k_4247_);
v___x_4249_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4250_, lean_object* v_k_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4250_, v_k_4251_);
lean_dec_ref(v_k_4251_);
return v_res_4252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = 1;
v___x_4260_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4260_, v___x_4259_);
return v___x_4261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4264_ = lean_string_append(v___x_4263_, v___x_4262_);
return v___x_4264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = 1;
v___x_4268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4269_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4268_, v___x_4267_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4271_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4272_ = lean_string_append(v___x_4271_, v___x_4270_);
return v___x_4272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4275_ = lean_string_append(v___x_4274_, v___x_4273_);
return v___x_4275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = 1;
v___x_4280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4280_, v___x_4279_);
return v___x_4281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4284_ = lean_string_append(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4286_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4287_ = lean_string_append(v___x_4286_, v___x_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4288_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4288_);
v___x_4290_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4288_, v___x_4289_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_json_4288_);
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4293_ = v___x_4290_;
v_isShared_4294_ = v_isSharedCheck_4300_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4300_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4298_; 
v___x_4295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4296_ = lean_string_append(v___x_4295_, v_a_4291_);
lean_dec(v_a_4291_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4296_);
v___x_4298_ = v___x_4293_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
else
{
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_json_4288_);
v_a_4301_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4290_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4290_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 0);
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4309_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4290_, 1);
v___x_4310_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4311_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4288_, v___x_4310_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4309_);
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4321_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4317_ = lean_string_append(v___x_4316_, v_a_4312_);
lean_dec(v_a_4312_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4317_);
v___x_4319_ = v___x_4314_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
else
{
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_a_4309_);
v_a_4322_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4311_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4311_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
lean_ctor_set_tag(v___x_4324_, 0);
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4338_; 
v_a_4330_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4332_ = v___x_4311_;
v_isShared_4333_ = v_isSharedCheck_4338_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4311_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4338_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v_a_4309_);
lean_ctor_set(v___x_4334_, 1, v_a_4330_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4334_);
v___x_4336_ = v___x_4332_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4341_, size_t v_i_4342_, lean_object* v_bs_4343_){
_start:
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
if (v___x_4344_ == 0)
{
return v_bs_4343_;
}
else
{
lean_object* v_v_4345_; lean_object* v___x_4346_; lean_object* v_bs_x27_4347_; lean_object* v___x_4348_; size_t v___x_4349_; size_t v___x_4350_; lean_object* v___x_4351_; 
v_v_4345_ = lean_array_uget(v_bs_4343_, v_i_4342_);
v___x_4346_ = lean_unsigned_to_nat(0u);
v_bs_x27_4347_ = lean_array_uset(v_bs_4343_, v_i_4342_, v___x_4346_);
v___x_4348_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4345_);
v___x_4349_ = ((size_t)1ULL);
v___x_4350_ = lean_usize_add(v_i_4342_, v___x_4349_);
v___x_4351_ = lean_array_uset(v_bs_x27_4347_, v_i_4342_, v___x_4348_);
v_i_4342_ = v___x_4350_;
v_bs_4343_ = v___x_4351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4353_, lean_object* v_i_4354_, lean_object* v_bs_4355_){
_start:
{
size_t v_sz_boxed_4356_; size_t v_i_boxed_4357_; lean_object* v_res_4358_; 
v_sz_boxed_4356_ = lean_unbox_usize(v_sz_4353_);
lean_dec(v_sz_4353_);
v_i_boxed_4357_ = lean_unbox_usize(v_i_4354_);
lean_dec(v_i_4354_);
v_res_4358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4356_, v_i_boxed_4357_, v_bs_4355_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4359_){
_start:
{
size_t v_sz_4360_; size_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_sz_4360_ = lean_array_size(v_a_4359_);
v___x_4361_ = ((size_t)0ULL);
v___x_4362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4360_, v___x_4361_, v_a_4359_);
v___x_4363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4364_){
_start:
{
lean_object* v_sourceRequestID_4365_; lean_object* v_queries_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4404_; 
v_sourceRequestID_4365_ = lean_ctor_get(v_x_4364_, 0);
v_queries_4366_ = lean_ctor_get(v_x_4364_, 1);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_x_4364_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4368_ = v_x_4364_;
v_isShared_4369_ = v_isSharedCheck_4404_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_queries_4366_);
lean_inc(v_sourceRequestID_4365_);
lean_dec(v_x_4364_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4404_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___y_4372_; 
v___x_4370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4365_))
{
case 0:
{
lean_object* v_s_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
v_s_4387_ = lean_ctor_get(v_sourceRequestID_4365_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_sourceRequestID_4365_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v_sourceRequestID_4365_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_s_4387_);
lean_dec(v_sourceRequestID_4365_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
lean_ctor_set_tag(v___x_4389_, 3);
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_s_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
v___y_4372_ = v___x_4392_;
goto v___jp_4371_;
}
}
}
case 1:
{
lean_object* v_n_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
v_n_4395_ = lean_ctor_get(v_sourceRequestID_4365_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_sourceRequestID_4365_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v_sourceRequestID_4365_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_n_4395_);
lean_dec(v_sourceRequestID_4365_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
lean_ctor_set_tag(v___x_4397_, 2);
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_n_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
v___y_4372_ = v___x_4400_;
goto v___jp_4371_;
}
}
}
default: 
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_box(0);
v___y_4372_ = v___x_4403_;
goto v___jp_4371_;
}
}
v___jp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 1, v___y_4372_);
lean_ctor_set(v___x_4368_, 0, v___x_4370_);
v___x_4374_ = v___x_4368_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v___y_4372_);
v___x_4374_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4375_ = lean_box(0);
v___x_4376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4374_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4378_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4366_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
lean_ctor_set(v___x_4380_, 1, v___x_4375_);
v___x_4381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
lean_ctor_set(v___x_4381_, 1, v___x_4375_);
v___x_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4376_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4384_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4382_, v___x_4383_);
v___x_4385_ = l_Lean_Json_mkObj(v___x_4384_);
lean_dec(v___x_4384_);
return v___x_4385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4407_, lean_object* v_k_4408_){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = l_Lean_Json_getObjValD(v_j_4407_, v_k_4408_);
v___x_4410_ = l_Lean_Name_fromJson_x3f(v___x_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4411_, lean_object* v_k_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4411_, v_k_4412_);
lean_dec_ref(v_k_4412_);
return v_res_4413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = 1;
v___x_4421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4421_, v___x_4420_);
return v___x_4422_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4424_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4425_ = lean_string_append(v___x_4424_, v___x_4423_);
return v___x_4425_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = 1;
v___x_4429_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4430_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4432_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4433_ = lean_string_append(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4435_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4436_ = lean_string_append(v___x_4435_, v___x_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = 1;
v___x_4441_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4445_ = lean_string_append(v___x_4444_, v___x_4443_);
return v___x_4445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4447_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4448_ = lean_string_append(v___x_4447_, v___x_4446_);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = 1;
v___x_4453_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4454_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4453_, v___x_4452_);
return v___x_4454_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4456_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4457_ = lean_string_append(v___x_4456_, v___x_4455_);
return v___x_4457_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4459_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4460_ = lean_string_append(v___x_4459_, v___x_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4461_){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4461_);
v___x_4463_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4461_, v___x_4462_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4473_; 
lean_dec(v_json_4461_);
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4466_ = v___x_4463_;
v_isShared_4467_ = v_isSharedCheck_4473_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4463_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4473_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4468_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4469_ = lean_string_append(v___x_4468_, v_a_4464_);
lean_dec(v_a_4464_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 0, v___x_4469_);
v___x_4471_ = v___x_4466_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
else
{
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_json_4461_);
v_a_4474_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4463_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4463_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 0);
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
else
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4463_, 1);
v___x_4483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4461_);
v___x_4484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4461_, v___x_4483_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4494_; 
lean_dec(v_a_4482_);
lean_dec(v_json_4461_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4490_ = lean_string_append(v___x_4489_, v_a_4485_);
lean_dec(v_a_4485_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4490_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_a_4482_);
lean_dec(v_json_4461_);
v_a_4495_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4484_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 0);
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v_a_4503_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4484_, 1);
v___x_4504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4505_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4461_, v___x_4504_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4503_);
lean_dec(v_a_4482_);
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4508_ = v___x_4505_;
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4505_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4515_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4511_ = lean_string_append(v___x_4510_, v_a_4506_);
lean_dec(v_a_4506_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4511_);
v___x_4513_ = v___x_4508_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
else
{
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_a_4503_);
lean_dec(v_a_4482_);
v_a_4516_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4505_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4505_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
lean_ctor_set_tag(v___x_4518_, 0);
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4533_; 
v_a_4524_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4526_ = v___x_4505_;
v_isShared_4527_ = v_isSharedCheck_4533_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4505_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4533_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4531_; 
v___x_4528_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4528_, 0, v_a_4482_);
lean_ctor_set(v___x_4528_, 1, v_a_4503_);
v___x_4529_ = lean_unbox(v_a_4524_);
lean_dec(v_a_4524_);
lean_ctor_set_uint8(v___x_4528_, sizeof(void*)*2, v___x_4529_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4528_);
v___x_4531_ = v___x_4526_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4528_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4536_){
_start:
{
lean_object* v_module_4537_; lean_object* v_decl_4538_; uint8_t v_isExactMatch_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v_module_4537_ = lean_ctor_get(v_x_4536_, 0);
lean_inc(v_module_4537_);
v_decl_4538_ = lean_ctor_get(v_x_4536_, 1);
lean_inc(v_decl_4538_);
v_isExactMatch_4539_ = lean_ctor_get_uint8(v_x_4536_, sizeof(void*)*2);
lean_dec_ref(v_x_4536_);
v___x_4540_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4541_ = 1;
v___x_4542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4537_, v___x_4541_);
v___x_4543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
v___x_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4540_);
lean_ctor_set(v___x_4544_, 1, v___x_4543_);
v___x_4545_ = lean_box(0);
v___x_4546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4544_);
lean_ctor_set(v___x_4546_, 1, v___x_4545_);
v___x_4547_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4548_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4538_, v___x_4541_);
v___x_4549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
v___x_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4547_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
lean_ctor_set(v___x_4551_, 1, v___x_4545_);
v___x_4552_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4553_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4553_, 0, v_isExactMatch_4539_);
v___x_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
lean_ctor_set(v___x_4555_, 1, v___x_4545_);
v___x_4556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v___x_4545_);
v___x_4557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4551_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4546_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4560_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4558_, v___x_4559_);
v___x_4561_ = l_Lean_Json_mkObj(v___x_4560_);
lean_dec(v___x_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4564_, size_t v_i_4565_, lean_object* v_bs_4566_){
_start:
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_usize_dec_lt(v_i_4565_, v_sz_4564_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4568_, 0, v_bs_4566_);
return v___x_4568_;
}
else
{
lean_object* v_v_4569_; lean_object* v___x_4570_; 
v_v_4569_ = lean_array_uget_borrowed(v_bs_4566_, v_i_4565_);
lean_inc(v_v_4569_);
v___x_4570_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4569_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_bs_4566_);
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4580_; lean_object* v_bs_x27_4581_; size_t v___x_4582_; size_t v___x_4583_; lean_object* v___x_4584_; 
v_a_4579_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4570_, 1);
v___x_4580_ = lean_unsigned_to_nat(0u);
v_bs_x27_4581_ = lean_array_uset(v_bs_4566_, v_i_4565_, v___x_4580_);
v___x_4582_ = ((size_t)1ULL);
v___x_4583_ = lean_usize_add(v_i_4565_, v___x_4582_);
v___x_4584_ = lean_array_uset(v_bs_x27_4581_, v_i_4565_, v_a_4579_);
v_i_4565_ = v___x_4583_;
v_bs_4566_ = v___x_4584_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4586_, lean_object* v_i_4587_, lean_object* v_bs_4588_){
_start:
{
size_t v_sz_boxed_4589_; size_t v_i_boxed_4590_; lean_object* v_res_4591_; 
v_sz_boxed_4589_ = lean_unbox_usize(v_sz_4586_);
lean_dec(v_sz_4586_);
v_i_boxed_4590_ = lean_unbox_usize(v_i_4587_);
lean_dec(v_i_4587_);
v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4589_, v_i_boxed_4590_, v_bs_4588_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4592_){
_start:
{
if (lean_obj_tag(v_x_4592_) == 4)
{
lean_object* v_elems_4593_; size_t v_sz_4594_; size_t v___x_4595_; lean_object* v___x_4596_; 
v_elems_4593_ = lean_ctor_get(v_x_4592_, 0);
lean_inc_ref(v_elems_4593_);
lean_dec_ref_known(v_x_4592_, 1);
v_sz_4594_ = lean_array_size(v_elems_4593_);
v___x_4595_ = ((size_t)0ULL);
v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4594_, v___x_4595_, v_elems_4593_);
return v___x_4596_;
}
else
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4597_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4598_ = lean_unsigned_to_nat(80u);
v___x_4599_ = l_Lean_Json_pretty(v_x_4592_, v___x_4598_);
v___x_4600_ = lean_string_append(v___x_4597_, v___x_4599_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4602_ = lean_string_append(v___x_4600_, v___x_4601_);
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4604_, size_t v_i_4605_, lean_object* v_bs_4606_){
_start:
{
uint8_t v___x_4607_; 
v___x_4607_ = lean_usize_dec_lt(v_i_4605_, v_sz_4604_);
if (v___x_4607_ == 0)
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_bs_4606_);
return v___x_4608_;
}
else
{
lean_object* v_v_4609_; lean_object* v___x_4610_; 
v_v_4609_ = lean_array_uget_borrowed(v_bs_4606_, v_i_4605_);
lean_inc(v_v_4609_);
v___x_4610_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4609_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_dec_ref(v_bs_4606_);
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4620_; lean_object* v_bs_x27_4621_; size_t v___x_4622_; size_t v___x_4623_; lean_object* v___x_4624_; 
v_a_4619_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_a_4619_);
lean_dec_ref_known(v___x_4610_, 1);
v___x_4620_ = lean_unsigned_to_nat(0u);
v_bs_x27_4621_ = lean_array_uset(v_bs_4606_, v_i_4605_, v___x_4620_);
v___x_4622_ = ((size_t)1ULL);
v___x_4623_ = lean_usize_add(v_i_4605_, v___x_4622_);
v___x_4624_ = lean_array_uset(v_bs_x27_4621_, v_i_4605_, v_a_4619_);
v_i_4605_ = v___x_4623_;
v_bs_4606_ = v___x_4624_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4626_, lean_object* v_i_4627_, lean_object* v_bs_4628_){
_start:
{
size_t v_sz_boxed_4629_; size_t v_i_boxed_4630_; lean_object* v_res_4631_; 
v_sz_boxed_4629_ = lean_unbox_usize(v_sz_4626_);
lean_dec(v_sz_4626_);
v_i_boxed_4630_ = lean_unbox_usize(v_i_4627_);
lean_dec(v_i_4627_);
v_res_4631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4629_, v_i_boxed_4630_, v_bs_4628_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4632_){
_start:
{
if (lean_obj_tag(v_x_4632_) == 4)
{
lean_object* v_elems_4633_; size_t v_sz_4634_; size_t v___x_4635_; lean_object* v___x_4636_; 
v_elems_4633_ = lean_ctor_get(v_x_4632_, 0);
lean_inc_ref(v_elems_4633_);
lean_dec_ref_known(v_x_4632_, 1);
v_sz_4634_ = lean_array_size(v_elems_4633_);
v___x_4635_ = ((size_t)0ULL);
v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4634_, v___x_4635_, v_elems_4633_);
return v___x_4636_;
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4637_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4638_ = lean_unsigned_to_nat(80u);
v___x_4639_ = l_Lean_Json_pretty(v_x_4632_, v___x_4638_);
v___x_4640_ = lean_string_append(v___x_4637_, v___x_4639_);
lean_dec_ref(v___x_4639_);
v___x_4641_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4642_ = lean_string_append(v___x_4640_, v___x_4641_);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4644_, lean_object* v_k_4645_){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = l_Lean_Json_getObjValD(v_j_4644_, v_k_4645_);
v___x_4647_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4646_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4648_, lean_object* v_k_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4648_, v_k_4649_);
lean_dec_ref(v_k_4649_);
return v_res_4650_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = 1;
v___x_4658_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4659_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4658_, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4661_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4662_ = lean_string_append(v___x_4661_, v___x_4660_);
return v___x_4662_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = 1;
v___x_4666_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4670_ = lean_string_append(v___x_4669_, v___x_4668_);
return v___x_4670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4672_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4673_ = lean_string_append(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4674_){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4676_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4674_, v___x_4675_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4686_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4686_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4686_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4681_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4682_ = lean_string_append(v___x_4681_, v_a_4677_);
lean_dec(v_a_4677_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4682_);
v___x_4684_ = v___x_4679_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
else
{
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
v_a_4687_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4676_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4676_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 0);
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
v_a_4695_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4676_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4676_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4705_, size_t v_i_4706_, lean_object* v_bs_4707_){
_start:
{
uint8_t v___x_4708_; 
v___x_4708_ = lean_usize_dec_lt(v_i_4706_, v_sz_4705_);
if (v___x_4708_ == 0)
{
return v_bs_4707_;
}
else
{
lean_object* v_v_4709_; lean_object* v___x_4710_; lean_object* v_bs_x27_4711_; lean_object* v___x_4712_; size_t v___x_4713_; size_t v___x_4714_; lean_object* v___x_4715_; 
v_v_4709_ = lean_array_uget(v_bs_4707_, v_i_4706_);
v___x_4710_ = lean_unsigned_to_nat(0u);
v_bs_x27_4711_ = lean_array_uset(v_bs_4707_, v_i_4706_, v___x_4710_);
v___x_4712_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4709_);
v___x_4713_ = ((size_t)1ULL);
v___x_4714_ = lean_usize_add(v_i_4706_, v___x_4713_);
v___x_4715_ = lean_array_uset(v_bs_x27_4711_, v_i_4706_, v___x_4712_);
v_i_4706_ = v___x_4714_;
v_bs_4707_ = v___x_4715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4717_, lean_object* v_i_4718_, lean_object* v_bs_4719_){
_start:
{
size_t v_sz_boxed_4720_; size_t v_i_boxed_4721_; lean_object* v_res_4722_; 
v_sz_boxed_4720_ = lean_unbox_usize(v_sz_4717_);
lean_dec(v_sz_4717_);
v_i_boxed_4721_ = lean_unbox_usize(v_i_4718_);
lean_dec(v_i_4718_);
v_res_4722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4720_, v_i_boxed_4721_, v_bs_4719_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4723_){
_start:
{
size_t v_sz_4724_; size_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v_sz_4724_ = lean_array_size(v_a_4723_);
v___x_4725_ = ((size_t)0ULL);
v___x_4726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4724_, v___x_4725_, v_a_4723_);
v___x_4727_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4728_, size_t v_i_4729_, lean_object* v_bs_4730_){
_start:
{
uint8_t v___x_4731_; 
v___x_4731_ = lean_usize_dec_lt(v_i_4729_, v_sz_4728_);
if (v___x_4731_ == 0)
{
return v_bs_4730_;
}
else
{
lean_object* v_v_4732_; lean_object* v___x_4733_; lean_object* v_bs_x27_4734_; lean_object* v___x_4735_; size_t v___x_4736_; size_t v___x_4737_; lean_object* v___x_4738_; 
v_v_4732_ = lean_array_uget(v_bs_4730_, v_i_4729_);
v___x_4733_ = lean_unsigned_to_nat(0u);
v_bs_x27_4734_ = lean_array_uset(v_bs_4730_, v_i_4729_, v___x_4733_);
v___x_4735_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4732_);
v___x_4736_ = ((size_t)1ULL);
v___x_4737_ = lean_usize_add(v_i_4729_, v___x_4736_);
v___x_4738_ = lean_array_uset(v_bs_x27_4734_, v_i_4729_, v___x_4735_);
v_i_4729_ = v___x_4737_;
v_bs_4730_ = v___x_4738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4740_, lean_object* v_i_4741_, lean_object* v_bs_4742_){
_start:
{
size_t v_sz_boxed_4743_; size_t v_i_boxed_4744_; lean_object* v_res_4745_; 
v_sz_boxed_4743_ = lean_unbox_usize(v_sz_4740_);
lean_dec(v_sz_4740_);
v_i_boxed_4744_ = lean_unbox_usize(v_i_4741_);
lean_dec(v_i_4741_);
v_res_4745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4743_, v_i_boxed_4744_, v_bs_4742_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4746_){
_start:
{
size_t v_sz_4747_; size_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v_sz_4747_ = lean_array_size(v_a_4746_);
v___x_4748_ = ((size_t)0ULL);
v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4747_, v___x_4748_, v_a_4746_);
v___x_4750_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4752_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4753_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4751_);
v___x_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4752_);
lean_ctor_set(v___x_4754_, 1, v___x_4753_);
v___x_4755_ = lean_box(0);
v___x_4756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4754_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
lean_ctor_set(v___x_4757_, 1, v___x_4755_);
v___x_4758_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4759_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4757_, v___x_4758_);
v___x_4760_ = l_Lean_Json_mkObj(v___x_4759_);
lean_dec(v___x_4759_);
return v___x_4760_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4772_ = 1;
v___x_4773_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4773_, v___x_4772_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4777_ = lean_string_append(v___x_4776_, v___x_4775_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4778_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4779_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4780_ = lean_string_append(v___x_4779_, v___x_4778_);
return v___x_4780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4782_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4783_ = lean_string_append(v___x_4782_, v___x_4781_);
return v___x_4783_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4784_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4785_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4786_ = lean_string_append(v___x_4785_, v___x_4784_);
return v___x_4786_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4787_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4788_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4789_ = lean_string_append(v___x_4788_, v___x_4787_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4790_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4790_);
v___x_4792_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4790_, v___x_4791_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4802_; 
lean_dec(v_json_4790_);
v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4795_ = v___x_4792_;
v_isShared_4796_ = v_isSharedCheck_4802_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4792_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4802_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4797_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4798_ = lean_string_append(v___x_4797_, v_a_4793_);
lean_dec(v_a_4793_);
if (v_isShared_4796_ == 0)
{
lean_ctor_set(v___x_4795_, 0, v___x_4798_);
v___x_4800_ = v___x_4795_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
else
{
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v_json_4790_);
v_a_4803_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4792_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4792_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 0);
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v_a_4811_ = lean_ctor_get(v___x_4792_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4792_, 1);
v___x_4812_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4813_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4790_, v___x_4812_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v_a_4811_);
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4823_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4823_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___x_4818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4819_ = lean_string_append(v___x_4818_, v_a_4814_);
lean_dec(v_a_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4819_);
v___x_4821_ = v___x_4816_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec(v_a_4811_);
v_a_4824_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4813_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4813_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
lean_ctor_set_tag(v___x_4826_, 0);
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4840_; 
v_a_4832_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4834_ = v___x_4813_;
v_isShared_4835_ = v_isSharedCheck_4840_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4813_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4840_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4836_, 0, v_a_4811_);
lean_ctor_set(v___x_4836_, 1, v_a_4832_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v___x_4836_);
v___x_4838_ = v___x_4834_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4843_){
_start:
{
lean_object* v_module_4844_; lean_object* v_decl_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4868_; 
v_module_4844_ = lean_ctor_get(v_x_4843_, 0);
v_decl_4845_ = lean_ctor_get(v_x_4843_, 1);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_x_4843_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4847_ = v_x_4843_;
v_isShared_4848_ = v_isSharedCheck_4868_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_decl_4845_);
lean_inc(v_module_4844_);
lean_dec(v_x_4843_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4868_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; uint8_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___x_4849_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4850_ = 1;
v___x_4851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4844_, v___x_4850_);
v___x_4852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 1, v___x_4852_);
lean_ctor_set(v___x_4847_, 0, v___x_4849_);
v___x_4854_ = v___x_4847_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4854_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4858_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4845_, v___x_4850_);
v___x_4859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
v___x_4860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4857_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
lean_ctor_set(v___x_4861_, 1, v___x_4855_);
v___x_4862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v___x_4855_);
v___x_4863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4856_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4865_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4863_, v___x_4864_);
v___x_4866_ = l_Lean_Json_mkObj(v___x_4865_);
lean_dec(v___x_4865_);
return v___x_4866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4871_, lean_object* v_k_4872_){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = l_Lean_Json_getObjValD(v_j_4871_, v_k_4872_);
v___x_4874_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4873_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4875_, lean_object* v_k_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4875_, v_k_4876_);
lean_dec_ref(v_k_4876_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4880_){
_start:
{
if (lean_obj_tag(v_x_4880_) == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4881_;
}
else
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4880_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4882_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4899_; 
v_a_4891_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4893_ = v___x_4882_;
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4882_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4895_; lean_object* v___x_4897_; 
v___x_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4895_, 0, v_a_4891_);
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4895_);
v___x_4897_ = v___x_4893_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4900_, lean_object* v_k_4901_){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = l_Lean_Json_getObjValD(v_j_4900_, v_k_4901_);
v___x_4903_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4904_, lean_object* v_k_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4904_, v_k_4905_);
lean_dec_ref(v_k_4905_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4909_){
_start:
{
if (lean_obj_tag(v_x_4909_) == 0)
{
lean_object* v___x_4910_; 
v___x_4910_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4910_;
}
else
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4909_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4928_; 
v_a_4920_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4922_ = v___x_4911_;
v_isShared_4923_ = v_isSharedCheck_4928_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4911_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4928_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4924_, 0, v_a_4920_);
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 0, v___x_4924_);
v___x_4926_ = v___x_4922_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4929_, lean_object* v_k_4930_){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4931_ = l_Lean_Json_getObjValD(v_j_4929_, v_k_4930_);
v___x_4932_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4933_, lean_object* v_k_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4933_, v_k_4934_);
lean_dec_ref(v_k_4934_);
return v_res_4935_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4942_ = 1;
v___x_4943_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4944_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4943_, v___x_4942_);
return v___x_4944_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4945_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4946_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4947_ = lean_string_append(v___x_4946_, v___x_4945_);
return v___x_4947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = 1;
v___x_4952_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4953_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4952_, v___x_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4954_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4955_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4956_ = lean_string_append(v___x_4955_, v___x_4954_);
return v___x_4956_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4958_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4959_ = lean_string_append(v___x_4958_, v___x_4957_);
return v___x_4959_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4963_ = 1;
v___x_4964_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4965_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4964_, v___x_4963_);
return v___x_4965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4968_ = lean_string_append(v___x_4967_, v___x_4966_);
return v___x_4968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4970_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4971_ = lean_string_append(v___x_4970_, v___x_4969_);
return v___x_4971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4975_ = 1;
v___x_4976_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4976_, v___x_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4980_ = lean_string_append(v___x_4979_, v___x_4978_);
return v___x_4980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4983_ = lean_string_append(v___x_4982_, v___x_4981_);
return v___x_4983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = 1;
v___x_4988_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4988_, v___x_4987_);
return v___x_4989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4992_ = lean_string_append(v___x_4991_, v___x_4990_);
return v___x_4992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4995_ = lean_string_append(v___x_4994_, v___x_4993_);
return v___x_4995_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = 1;
v___x_5001_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_5002_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5001_, v___x_5000_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_5004_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5005_ = lean_string_append(v___x_5004_, v___x_5003_);
return v___x_5005_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5006_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5007_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5008_ = lean_string_append(v___x_5007_, v___x_5006_);
return v___x_5008_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5012_ = 1;
v___x_5013_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5013_, v___x_5012_);
return v___x_5014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5015_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5016_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5017_ = lean_string_append(v___x_5016_, v___x_5015_);
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5018_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5019_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5020_ = lean_string_append(v___x_5019_, v___x_5018_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5021_){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5021_);
v___x_5023_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5021_, v___x_5022_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v_json_5021_);
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5026_ = v___x_5023_;
v_isShared_5027_ = v_isSharedCheck_5033_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5033_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5028_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5029_ = lean_string_append(v___x_5028_, v_a_5024_);
lean_dec(v_a_5024_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5029_);
v___x_5031_ = v___x_5026_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
else
{
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_json_5021_);
v_a_5034_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5023_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5023_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
lean_ctor_set_tag(v___x_5036_, 0);
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v_a_5042_ = lean_ctor_get(v___x_5023_, 0);
lean_inc(v_a_5042_);
lean_dec_ref_known(v___x_5023_, 1);
v___x_5043_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5021_);
v___x_5044_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5021_, v___x_5043_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5054_; 
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5047_ = v___x_5044_;
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5052_; 
v___x_5049_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5050_ = lean_string_append(v___x_5049_, v_a_5045_);
lean_dec(v_a_5045_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v___x_5050_);
v___x_5052_ = v___x_5047_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
else
{
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5062_; 
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5055_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5057_ = v___x_5044_;
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_a_5055_);
lean_dec(v___x_5044_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5062_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5060_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set_tag(v___x_5057_, 0);
v___x_5060_ = v___x_5057_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5055_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
return v___x_5060_;
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5044_, 1);
v___x_5064_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5021_);
v___x_5065_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5021_, v___x_5064_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5068_ = v___x_5065_;
v_isShared_5069_ = v_isSharedCheck_5075_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_5065_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5075_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5073_; 
v___x_5070_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5071_ = lean_string_append(v___x_5070_, v_a_5066_);
lean_dec(v_a_5066_);
if (v_isShared_5069_ == 0)
{
lean_ctor_set(v___x_5068_, 0, v___x_5071_);
v___x_5073_ = v___x_5068_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
else
{
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5076_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5065_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5065_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
lean_ctor_set_tag(v___x_5078_, 0);
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v_a_5084_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5085_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5021_);
v___x_5086_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5021_, v___x_5085_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5096_; 
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5089_ = v___x_5086_;
v_isShared_5090_ = v_isSharedCheck_5096_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5086_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5096_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5091_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5092_ = lean_string_append(v___x_5091_, v_a_5087_);
lean_dec(v_a_5087_);
if (v_isShared_5090_ == 0)
{
lean_ctor_set(v___x_5089_, 0, v___x_5092_);
v___x_5094_ = v___x_5089_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5092_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
else
{
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5097_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5086_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5086_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 0);
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v_a_5105_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5086_, 1);
v___x_5106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5021_);
v___x_5107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5021_, v___x_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v_a_5105_);
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5110_ = v___x_5107_;
v_isShared_5111_ = v_isSharedCheck_5117_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5107_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5117_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5115_; 
v___x_5112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5113_ = lean_string_append(v___x_5112_, v_a_5108_);
lean_dec(v_a_5108_);
if (v_isShared_5111_ == 0)
{
lean_ctor_set(v___x_5110_, 0, v___x_5113_);
v___x_5115_ = v___x_5110_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
else
{
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec(v_a_5105_);
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
lean_dec(v_json_5021_);
v_a_5118_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5107_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5107_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
lean_ctor_set_tag(v___x_5120_, 0);
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_a_5126_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5107_, 1);
v___x_5127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5128_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5021_, v___x_5127_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5138_; 
lean_dec(v_a_5126_);
lean_dec(v_a_5105_);
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5131_ = v___x_5128_;
v_isShared_5132_ = v_isSharedCheck_5138_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5128_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5138_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5136_; 
v___x_5133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5134_ = lean_string_append(v___x_5133_, v_a_5129_);
lean_dec(v_a_5129_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 0, v___x_5134_);
v___x_5136_ = v___x_5131_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
else
{
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec(v_a_5126_);
lean_dec(v_a_5105_);
lean_dec(v_a_5084_);
lean_dec(v_a_5063_);
lean_dec(v_a_5042_);
v_a_5139_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_5128_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5128_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
lean_ctor_set_tag(v___x_5141_, 0);
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5157_; 
v_a_5147_ = lean_ctor_get(v___x_5128_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5128_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5149_ = v___x_5128_;
v_isShared_5150_ = v_isSharedCheck_5157_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5128_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5157_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; uint8_t v___x_5153_; lean_object* v___x_5155_; 
v___x_5151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5151_, 0, v_a_5042_);
lean_ctor_set(v___x_5151_, 1, v_a_5063_);
lean_ctor_set(v___x_5151_, 2, v_a_5084_);
lean_ctor_set(v___x_5151_, 3, v_a_5105_);
v___x_5152_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5152_, 0, v___x_5151_);
lean_ctor_set(v___x_5152_, 1, v_a_5126_);
v___x_5153_ = lean_unbox(v_a_5147_);
lean_dec(v_a_5147_);
lean_ctor_set_uint8(v___x_5152_, sizeof(void*)*2, v___x_5153_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5152_);
v___x_5155_ = v___x_5149_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5152_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5160_, lean_object* v_x_5161_){
_start:
{
if (lean_obj_tag(v_x_5161_) == 0)
{
lean_object* v___x_5162_; 
lean_dec_ref(v_k_5160_);
v___x_5162_ = lean_box(0);
return v___x_5162_;
}
else
{
lean_object* v_val_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v_val_5163_ = lean_ctor_get(v_x_5161_, 0);
lean_inc(v_val_5163_);
lean_dec_ref_known(v_x_5161_, 1);
v___x_5164_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5163_);
v___x_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5165_, 0, v_k_5160_);
lean_ctor_set(v___x_5165_, 1, v___x_5164_);
v___x_5166_ = lean_box(0);
v___x_5167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5165_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
return v___x_5167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5168_, lean_object* v_x_5169_){
_start:
{
if (lean_obj_tag(v_x_5169_) == 0)
{
lean_object* v___x_5170_; 
lean_dec_ref(v_k_5168_);
v___x_5170_ = lean_box(0);
return v___x_5170_;
}
else
{
lean_object* v_val_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v_val_5171_ = lean_ctor_get(v_x_5169_, 0);
lean_inc(v_val_5171_);
lean_dec_ref_known(v_x_5169_, 1);
v___x_5172_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5171_);
v___x_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5173_, 0, v_k_5168_);
lean_ctor_set(v___x_5173_, 1, v___x_5172_);
v___x_5174_ = lean_box(0);
v___x_5175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5173_);
lean_ctor_set(v___x_5175_, 1, v___x_5174_);
return v___x_5175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5176_){
_start:
{
lean_object* v_toLocationLink_5177_; lean_object* v_ident_x3f_5178_; uint8_t v_isDefault_5179_; lean_object* v_originSelectionRange_x3f_5180_; lean_object* v_targetUri_5181_; lean_object* v_targetRange_5182_; lean_object* v_targetSelectionRange_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v_toLocationLink_5177_ = lean_ctor_get(v_x_5176_, 0);
lean_inc_ref(v_toLocationLink_5177_);
v_ident_x3f_5178_ = lean_ctor_get(v_x_5176_, 1);
lean_inc(v_ident_x3f_5178_);
v_isDefault_5179_ = lean_ctor_get_uint8(v_x_5176_, sizeof(void*)*2);
lean_dec_ref(v_x_5176_);
v_originSelectionRange_x3f_5180_ = lean_ctor_get(v_toLocationLink_5177_, 0);
lean_inc(v_originSelectionRange_x3f_5180_);
v_targetUri_5181_ = lean_ctor_get(v_toLocationLink_5177_, 1);
lean_inc_ref(v_targetUri_5181_);
v_targetRange_5182_ = lean_ctor_get(v_toLocationLink_5177_, 2);
lean_inc_ref(v_targetRange_5182_);
v_targetSelectionRange_5183_ = lean_ctor_get(v_toLocationLink_5177_, 3);
lean_inc_ref(v_targetSelectionRange_5183_);
lean_dec_ref(v_toLocationLink_5177_);
v___x_5184_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5185_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5184_, v_originSelectionRange_x3f_5180_);
v___x_5186_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5187_, 0, v_targetUri_5181_);
v___x_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5186_);
lean_ctor_set(v___x_5188_, 1, v___x_5187_);
v___x_5189_ = lean_box(0);
v___x_5190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5188_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5192_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5182_);
v___x_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5191_);
lean_ctor_set(v___x_5193_, 1, v___x_5192_);
v___x_5194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
lean_ctor_set(v___x_5194_, 1, v___x_5189_);
v___x_5195_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5196_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5183_);
v___x_5197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5197_, 0, v___x_5195_);
lean_ctor_set(v___x_5197_, 1, v___x_5196_);
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
lean_ctor_set(v___x_5198_, 1, v___x_5189_);
v___x_5199_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5200_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5199_, v_ident_x3f_5178_);
v___x_5201_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5202_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5202_, 0, v_isDefault_5179_);
v___x_5203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5201_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
lean_ctor_set(v___x_5204_, 1, v___x_5189_);
v___x_5205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
lean_ctor_set(v___x_5205_, 1, v___x_5189_);
v___x_5206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5200_);
lean_ctor_set(v___x_5206_, 1, v___x_5205_);
v___x_5207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5198_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5194_);
lean_ctor_set(v___x_5208_, 1, v___x_5207_);
v___x_5209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5190_);
lean_ctor_set(v___x_5209_, 1, v___x_5208_);
v___x_5210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5185_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
v___x_5211_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5212_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5210_, v___x_5211_);
v___x_5213_ = l_Lean_Json_mkObj(v___x_5212_);
lean_dec(v___x_5212_);
return v___x_5213_;
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

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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDecls___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDecls___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__6_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__7_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__7_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__8_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__3_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDecls___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__9_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__10_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__11_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDecls___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDecls___lam__2, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__11_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__1_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDecls___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDecls = (const lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__12_value;
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
static const lean_closure_object l_Lean_Lsp_instFromJsonRefInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRefInfo___lam__1, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__3_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__11_value),((lean_object*)&l_Lean_Lsp_instFromJsonRefInfo___closed__0_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleRefs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleRefs___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDecls___closed__11_value),((lean_object*)&l_Lean_Lsp_instFromJsonModuleRefs___closed__0_value)} };
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
lean_dec_ref(v___x_39_);
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
lean_dec_ref(v___x_51_);
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
lean_dec_ref(v___x_63_);
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
lean_object* v_moduleName_203_; lean_object* v_identName_204_; lean_object* v_moduleName_205_; lean_object* v_identName_206_; 
v_moduleName_203_ = lean_ctor_get(v_x_187_, 0);
v_identName_204_ = lean_ctor_get(v_x_187_, 1);
v_moduleName_205_ = lean_ctor_get(v_x_188_, 0);
v_identName_206_ = lean_ctor_get(v_x_188_, 1);
v_a_190_ = v_moduleName_203_;
v_a_191_ = v_identName_204_;
v_b_192_ = v_moduleName_205_;
v_b_193_ = v_identName_206_;
goto v___jp_189_;
}
else
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
}
else
{
if (lean_obj_tag(v_x_188_) == 0)
{
uint8_t v___x_208_; 
v___x_208_ = 2;
return v___x_208_;
}
else
{
lean_object* v_moduleName_209_; lean_object* v_id_210_; lean_object* v_moduleName_211_; lean_object* v_id_212_; 
v_moduleName_209_ = lean_ctor_get(v_x_187_, 0);
v_id_210_ = lean_ctor_get(v_x_187_, 1);
v_moduleName_211_ = lean_ctor_get(v_x_188_, 0);
v_id_212_ = lean_ctor_get(v_x_188_, 1);
v_a_190_ = v_moduleName_209_;
v_a_191_ = v_id_210_;
v_b_192_ = v_moduleName_211_;
v_b_193_ = v_id_212_;
goto v___jp_189_;
}
}
v___jp_189_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_string_dec_lt(v_a_190_, v_b_192_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
v___x_195_ = lean_string_dec_eq(v_a_190_, v_b_192_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
v___x_196_ = 2;
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = lean_string_dec_lt(v_a_191_, v_b_193_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = lean_string_dec_eq(v_a_191_, v_b_193_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; 
v___x_199_ = 2;
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 1;
return v___x_200_;
}
}
else
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
}
}
else
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent_ord___boxed(lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Lean_Lsp_instOrdRefIdent_ord(v_x_213_, v_x_214_);
lean_dec_ref(v_x_214_);
lean_dec_ref(v_x_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx(lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(0u);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(1u);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx(v_x_222_);
lean_dec_ref(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(lean_object* v_t_224_, lean_object* v_k_225_){
_start:
{
lean_object* v_m_226_; lean_object* v_n_227_; lean_object* v___x_228_; 
v_m_226_ = lean_ctor_get(v_t_224_, 0);
lean_inc_ref(v_m_226_);
v_n_227_ = lean_ctor_get(v_t_224_, 1);
lean_inc_ref(v_n_227_);
lean_dec_ref(v_t_224_);
v___x_228_ = lean_apply_2(v_k_225_, v_m_226_, v_n_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(lean_object* v_motive_229_, lean_object* v_ctorIdx_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_k_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_231_, v_k_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___boxed(lean_object* v_motive_235_, lean_object* v_ctorIdx_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_k_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(v_motive_235_, v_ctorIdx_236_, v_t_237_, v_h_238_, v_k_239_);
lean_dec(v_ctorIdx_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim___redArg(lean_object* v_t_241_, lean_object* v_c_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_241_, v_c_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim(lean_object* v_motive_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_c_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_245_, v_c_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim___redArg(lean_object* v_t_249_, lean_object* v_f_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_249_, v_f_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_f_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_253_, v_f_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(lean_object* v_json_290_){
_start:
{
lean_object* v___x_291_; 
lean_inc(v_json_290_);
v___x_291_ = l_Lean_Json_getTag_x3f(v_json_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_292_; 
lean_dec(v_json_290_);
v___x_292_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1));
return v___x_292_;
}
else
{
lean_object* v_val_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_val_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v___x_291_);
v___x_294_ = lean_box(0);
v___x_295_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_296_ = lean_string_dec_eq(v_val_293_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_298_ = lean_string_dec_eq(v_val_293_, v___x_297_);
lean_dec(v_val_293_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_json_290_);
v___x_299_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5));
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_unsigned_to_nat(2u);
v___x_301_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11));
v___x_302_ = l_Lean_Json_parseCtorFields(v_json_290_, v___x_297_, v___x_300_, v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_a_311_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_302_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_array_get_borrowed(v___x_294_, v_a_311_, v___x_312_);
lean_inc(v___x_313_);
v___x_314_ = l_Lean_Json_getStr_x3f(v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_a_311_);
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_a_323_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_314_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_array_get(v___x_294_, v_a_311_, v___x_324_);
lean_dec(v_a_311_);
v___x_326_ = l_Lean_Json_getStr_x3f(v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_a_323_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_a_335_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_326_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_326_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_a_323_);
lean_ctor_set(v___x_339_, 1, v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_val_293_);
v___x_344_ = lean_unsigned_to_nat(2u);
v___x_345_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15));
v___x_346_ = l_Lean_Json_parseCtorFields(v_json_290_, v___x_295_, v___x_344_, v___x_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_355_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_346_);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_array_get_borrowed(v___x_294_, v_a_355_, v___x_356_);
lean_inc(v___x_357_);
v___x_358_ = l_Lean_Json_getStr_x3f(v___x_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_355_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_367_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_358_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_array_get(v___x_294_, v_a_355_, v___x_368_);
lean_dec(v_a_355_);
v___x_370_ = l_Lean_Json_getStr_x3f(v___x_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_a_379_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_381_ = v___x_370_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_370_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v_a_367_);
lean_ctor_set(v___x_383_, 1, v_a_379_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_m_391_; lean_object* v_n_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_412_; 
v_m_391_ = lean_ctor_get(v_x_390_, 0);
v_n_392_ = lean_ctor_get(v_x_390_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_412_ == 0)
{
v___x_394_ = v_x_390_;
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_n_392_);
lean_inc(v_m_391_);
lean_dec(v_x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_396_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_397_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_398_, 0, v_m_391_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v___x_398_);
lean_ctor_set(v___x_394_, 0, v___x_397_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_411_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_401_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8));
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v_n_392_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_Json_mkObj(v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_396_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_404_);
v___x_410_ = l_Lean_Json_mkObj(v___x_409_);
return v___x_410_;
}
}
}
else
{
lean_object* v_m_413_; lean_object* v_i_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_434_; 
v_m_413_ = lean_ctor_get(v_x_390_, 0);
v_i_414_ = lean_ctor_get(v_x_390_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_434_ == 0)
{
v___x_416_ = v_x_390_;
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_i_414_);
lean_inc(v_m_413_);
lean_dec(v_x_390_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_434_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_418_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_419_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_420_, 0, v_m_413_);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 0);
lean_ctor_set(v___x_416_, 1, v___x_420_);
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_420_);
v___x_422_ = v_reuseFailAlloc_433_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_423_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12));
v___x_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_424_, 0, v_i_414_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_422_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_Json_mkObj(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_418_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_426_);
v___x_432_ = l_Lean_Json_mkObj(v___x_431_);
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_moduleName_438_; lean_object* v_identName_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_moduleName_438_ = lean_ctor_get(v_x_437_, 0);
v_identName_439_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_identName_439_);
lean_inc(v_moduleName_438_);
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_moduleName_438_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_identName_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_moduleName_447_; lean_object* v_id_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_moduleName_447_ = lean_ctor_get(v_x_437_, 0);
v_id_448_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_x_437_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_id_448_);
lean_inc(v_moduleName_447_);
lean_dec(v_x_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_moduleName_447_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_id_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v_m_457_; lean_object* v_n_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_m_457_ = lean_ctor_get(v_x_456_, 0);
v_n_458_ = lean_ctor_get(v_x_456_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v_x_456_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_n_458_);
lean_inc(v_m_457_);
lean_dec(v_x_456_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_m_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_n_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v_m_466_; lean_object* v_i_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_m_466_ = lean_ctor_get(v_x_456_, 0);
v_i_467_ = lean_ctor_get(v_x_456_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_456_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v_x_456_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_i_467_);
lean_inc(v_m_466_);
lean_dec(v_x_456_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_m_466_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_i_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* v_s_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(v_s_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
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
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_a_485_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_493_ == 0)
{
v___x_487_ = v___x_476_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_476_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = l_Lean_Lsp_RefIdent_fromJsonRepr(v_a_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* v_id_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = l_Lean_Lsp_RefIdent_toJsonRepr(v_id_494_);
v___x_496_ = l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object* v_r_501_){
_start:
{
lean_object* v_range_502_; lean_object* v_pos_503_; lean_object* v_endPos_504_; lean_object* v_selectionRange_505_; lean_object* v_pos_506_; lean_object* v_endPos_507_; lean_object* v_charUtf16_508_; lean_object* v_endCharUtf16_509_; lean_object* v_line_510_; lean_object* v_line_511_; lean_object* v_charUtf16_512_; lean_object* v_endCharUtf16_513_; lean_object* v_line_514_; lean_object* v_line_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_range_502_ = lean_ctor_get(v_r_501_, 0);
v_pos_503_ = lean_ctor_get(v_range_502_, 0);
v_endPos_504_ = lean_ctor_get(v_range_502_, 2);
v_selectionRange_505_ = lean_ctor_get(v_r_501_, 1);
v_pos_506_ = lean_ctor_get(v_selectionRange_505_, 0);
v_endPos_507_ = lean_ctor_get(v_selectionRange_505_, 2);
v_charUtf16_508_ = lean_ctor_get(v_range_502_, 1);
v_endCharUtf16_509_ = lean_ctor_get(v_range_502_, 3);
v_line_510_ = lean_ctor_get(v_pos_503_, 0);
v_line_511_ = lean_ctor_get(v_endPos_504_, 0);
v_charUtf16_512_ = lean_ctor_get(v_selectionRange_505_, 1);
v_endCharUtf16_513_ = lean_ctor_get(v_selectionRange_505_, 3);
v_line_514_ = lean_ctor_get(v_pos_506_, 0);
v_line_515_ = lean_ctor_get(v_endPos_507_, 0);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_sub(v_line_510_, v___x_516_);
v___x_518_ = lean_nat_sub(v_line_511_, v___x_516_);
v___x_519_ = lean_nat_sub(v_line_514_, v___x_516_);
v___x_520_ = lean_nat_sub(v_line_515_, v___x_516_);
lean_inc(v_endCharUtf16_513_);
lean_inc(v_charUtf16_512_);
lean_inc(v_endCharUtf16_509_);
lean_inc(v_charUtf16_508_);
v___x_521_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_521_, 0, v___x_517_);
lean_ctor_set(v___x_521_, 1, v_charUtf16_508_);
lean_ctor_set(v___x_521_, 2, v___x_518_);
lean_ctor_set(v___x_521_, 3, v_endCharUtf16_509_);
lean_ctor_set(v___x_521_, 4, v___x_519_);
lean_ctor_set(v___x_521_, 5, v_charUtf16_512_);
lean_ctor_set(v___x_521_, 6, v___x_520_);
lean_ctor_set(v___x_521_, 7, v_endCharUtf16_513_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object* v_r_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_r_522_);
lean_dec_ref(v_r_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object* v_i_524_){
_start:
{
lean_object* v_rangeStartPosLine_525_; lean_object* v_rangeStartPosCharacter_526_; lean_object* v_rangeEndPosLine_527_; lean_object* v_rangeEndPosCharacter_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_rangeStartPosLine_525_ = lean_ctor_get(v_i_524_, 0);
v_rangeStartPosCharacter_526_ = lean_ctor_get(v_i_524_, 1);
v_rangeEndPosLine_527_ = lean_ctor_get(v_i_524_, 2);
v_rangeEndPosCharacter_528_ = lean_ctor_get(v_i_524_, 3);
lean_inc(v_rangeStartPosCharacter_526_);
lean_inc(v_rangeStartPosLine_525_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_rangeStartPosLine_525_);
lean_ctor_set(v___x_529_, 1, v_rangeStartPosCharacter_526_);
lean_inc(v_rangeEndPosCharacter_528_);
lean_inc(v_rangeEndPosLine_527_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_rangeEndPosLine_527_);
lean_ctor_set(v___x_530_, 1, v_rangeEndPosCharacter_528_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object* v_i_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Lsp_DeclInfo_range(v_i_532_);
lean_dec_ref(v_i_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object* v_i_534_){
_start:
{
lean_object* v_selectionRangeStartPosLine_535_; lean_object* v_selectionRangeStartPosCharacter_536_; lean_object* v_selectionRangeEndPosLine_537_; lean_object* v_selectionRangeEndPosCharacter_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_selectionRangeStartPosLine_535_ = lean_ctor_get(v_i_534_, 4);
v_selectionRangeStartPosCharacter_536_ = lean_ctor_get(v_i_534_, 5);
v_selectionRangeEndPosLine_537_ = lean_ctor_get(v_i_534_, 6);
v_selectionRangeEndPosCharacter_538_ = lean_ctor_get(v_i_534_, 7);
lean_inc(v_selectionRangeStartPosCharacter_536_);
lean_inc(v_selectionRangeStartPosLine_535_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_selectionRangeStartPosLine_535_);
lean_ctor_set(v___x_539_, 1, v_selectionRangeStartPosCharacter_536_);
lean_inc(v_selectionRangeEndPosCharacter_538_);
lean_inc(v_selectionRangeEndPosLine_537_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_selectionRangeEndPosLine_537_);
lean_ctor_set(v___x_540_, 1, v_selectionRangeEndPosCharacter_538_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object* v_i_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Lsp_DeclInfo_selectionRange(v_i_542_);
lean_dec_ref(v_i_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object* v_i_544_){
_start:
{
lean_object* v_rangeStartPosLine_545_; lean_object* v_rangeStartPosCharacter_546_; lean_object* v_rangeEndPosLine_547_; lean_object* v_rangeEndPosCharacter_548_; lean_object* v_selectionRangeStartPosLine_549_; lean_object* v_selectionRangeStartPosCharacter_550_; lean_object* v_selectionRangeEndPosLine_551_; lean_object* v_selectionRangeEndPosCharacter_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_rangeStartPosLine_545_ = lean_ctor_get(v_i_544_, 0);
lean_inc(v_rangeStartPosLine_545_);
v_rangeStartPosCharacter_546_ = lean_ctor_get(v_i_544_, 1);
lean_inc(v_rangeStartPosCharacter_546_);
v_rangeEndPosLine_547_ = lean_ctor_get(v_i_544_, 2);
lean_inc(v_rangeEndPosLine_547_);
v_rangeEndPosCharacter_548_ = lean_ctor_get(v_i_544_, 3);
lean_inc(v_rangeEndPosCharacter_548_);
v_selectionRangeStartPosLine_549_ = lean_ctor_get(v_i_544_, 4);
lean_inc(v_selectionRangeStartPosLine_549_);
v_selectionRangeStartPosCharacter_550_ = lean_ctor_get(v_i_544_, 5);
lean_inc(v_selectionRangeStartPosCharacter_550_);
v_selectionRangeEndPosLine_551_ = lean_ctor_get(v_i_544_, 6);
lean_inc(v_selectionRangeEndPosLine_551_);
v_selectionRangeEndPosCharacter_552_ = lean_ctor_get(v_i_544_, 7);
lean_inc(v_selectionRangeEndPosCharacter_552_);
lean_dec_ref(v_i_544_);
v___x_553_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_545_);
v___x_554_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___x_555_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_546_);
v___x_556_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_547_);
v___x_558_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_548_);
v___x_560_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_549_);
v___x_562_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_550_);
v___x_564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_551_);
v___x_566_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
v___x_567_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_552_);
v___x_568_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(8u);
v___x_570_ = lean_mk_empty_array_with_capacity(v___x_569_);
v___x_571_ = lean_array_push(v___x_570_, v___x_554_);
v___x_572_ = lean_array_push(v___x_571_, v___x_556_);
v___x_573_ = lean_array_push(v___x_572_, v___x_558_);
v___x_574_ = lean_array_push(v___x_573_, v___x_560_);
v___x_575_ = lean_array_push(v___x_574_, v___x_562_);
v___x_576_ = lean_array_push(v___x_575_, v___x_564_);
v___x_577_ = lean_array_push(v___x_576_, v___x_566_);
v___x_578_ = lean_array_push(v___x_577_, v___x_568_);
v___x_579_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object* v___x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 4)
{
lean_object* v_elems_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_705_; 
v_elems_588_ = lean_ctor_get(v_x_587_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_705_ == 0)
{
v___x_590_ = v_x_587_;
v_isShared_591_ = v_isSharedCheck_705_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_elems_588_);
lean_dec(v_x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_705_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_get_size(v_elems_588_);
v___x_593_ = lean_unsigned_to_nat(8u);
v___x_594_ = lean_nat_dec_eq(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec_ref(v_elems_588_);
v___x_595_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_596_ = l_Nat_reprFast(v___x_592_);
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
lean_dec_ref(v___x_596_);
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 0);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_599_ = v___x_590_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_del_object(v___x_590_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_601_);
lean_inc(v___x_602_);
v___x_603_ = l_Lean_Json_getNat_x3f(v___x_602_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_603_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_613_);
lean_inc(v___x_614_);
v___x_615_ = l_Lean_Json_getNat_x3f(v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_615_);
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_625_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Json_getNat_x3f(v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_627_);
v___x_637_ = lean_unsigned_to_nat(3u);
v___x_638_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_637_);
lean_inc(v___x_638_);
v___x_639_ = l_Lean_Json_getNat_x3f(v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_639_);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_649_);
lean_inc(v___x_650_);
v___x_651_ = l_Lean_Json_getNat_x3f(v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_651_);
v___x_661_ = lean_unsigned_to_nat(5u);
v___x_662_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_661_);
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
lean_dec_ref(v_elems_588_);
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
lean_dec_ref(v___x_663_);
v___x_673_ = lean_unsigned_to_nat(6u);
v___x_674_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_673_);
lean_inc(v___x_674_);
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
lean_dec_ref(v_elems_588_);
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
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_684_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_684_);
lean_dec_ref(v___x_675_);
v___x_685_ = lean_unsigned_to_nat(7u);
v___x_686_ = lean_array_get(v___x_586_, v_elems_588_, v___x_685_);
lean_dec_ref(v_elems_588_);
v___x_687_ = l_Lean_Json_getNat_x3f(v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_684_);
lean_dec(v_a_672_);
lean_dec(v_a_660_);
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_dec(v_a_624_);
lean_dec(v_a_612_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_a_696_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_700_, 0, v_a_612_);
lean_ctor_set(v___x_700_, 1, v_a_624_);
lean_ctor_set(v___x_700_, 2, v_a_636_);
lean_ctor_set(v___x_700_, 3, v_a_648_);
lean_ctor_set(v___x_700_, 4, v_a_660_);
lean_ctor_set(v___x_700_, 5, v_a_672_);
lean_ctor_set(v___x_700_, 6, v_a_684_);
lean_ctor_set(v___x_700_, 7, v_a_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
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
lean_object* v___x_706_; 
lean_dec(v_x_587_);
v___x_706_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object* v___x_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Lsp_instFromJsonDeclInfo___lam__0(v___x_707_, v_x_708_);
lean_dec(v___x_707_);
return v_res_709_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(1);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(1);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_715_, lean_object* v_a_716_, lean_object* v_b_717_, lean_object* v_c_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_a_716_);
lean_ctor_set(v___x_719_, 1, v_b_717_);
v___x_720_ = lean_apply_2(v_f_715_, v___x_719_, v_c_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_740_, lean_object* v_init_741_, lean_object* v_f_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_743_, 0, v_f_742_);
v___x_744_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_745_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_744_, v___f_743_, v_init_741_, v_m_740_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec(v___x_745_);
return v_a_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_747_, lean_object* v_m_748_, lean_object* v_init_749_, lean_object* v_f_750_){
_start:
{
lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_a_754_; 
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_751_, 0, v_f_750_);
v___x_752_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_753_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_752_, v___f_751_, v_init_749_, v_m_748_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec(v___x_753_);
return v_a_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_755_, lean_object* v_init_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v_l_760_; lean_object* v_r_761_; lean_object* v___x_762_; 
v_k_758_ = lean_ctor_get(v_x_757_, 1);
v_v_759_ = lean_ctor_get(v_x_757_, 2);
v_l_760_ = lean_ctor_get(v_x_757_, 3);
v_r_761_ = lean_ctor_get(v_x_757_, 4);
lean_inc_ref(v___y_755_);
v___x_762_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_755_, v_init_756_, v_l_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref(v___y_755_);
return v___x_762_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
lean_inc(v_v_759_);
lean_inc(v_k_758_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_k_758_);
lean_ctor_set(v___x_764_, 1, v_v_759_);
lean_inc_ref(v___y_755_);
v___x_765_ = lean_apply_2(v___y_755_, v___x_764_, v_a_763_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref(v___y_755_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v___x_765_);
v_init_756_ = v_a_766_;
v_x_757_ = v_r_761_;
goto _start;
}
}
}
else
{
lean_object* v___x_768_; 
lean_dec_ref(v___y_755_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v_init_756_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_769_, lean_object* v_init_770_, lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_769_, v_init_770_, v_x_771_);
lean_dec(v_x_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_777_; lean_object* v_a_778_; 
v___x_777_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_776_, v___y_775_, v___y_774_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref(v___x_777_);
return v_a_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v_init_788_, lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_787_, v_init_788_, v_x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v_init_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_791_, v___y_792_, v_init_793_, v_x_794_);
lean_dec(v_x_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_796_){
_start:
{
lean_object* v_snd_797_; lean_object* v_fst_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_840_; 
v_snd_797_ = lean_ctor_get(v_x_796_, 1);
v_fst_798_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_840_ == 0)
{
v___x_800_ = v_x_796_;
v_isShared_801_ = v_isSharedCheck_840_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_797_);
lean_inc(v_fst_798_);
lean_dec(v_x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_840_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_rangeStartPosLine_802_; lean_object* v_rangeStartPosCharacter_803_; lean_object* v_rangeEndPosLine_804_; lean_object* v_rangeEndPosCharacter_805_; lean_object* v_selectionRangeStartPosLine_806_; lean_object* v_selectionRangeStartPosCharacter_807_; lean_object* v_selectionRangeEndPosLine_808_; lean_object* v_selectionRangeEndPosCharacter_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v_rangeStartPosLine_802_ = lean_ctor_get(v_snd_797_, 0);
lean_inc(v_rangeStartPosLine_802_);
v_rangeStartPosCharacter_803_ = lean_ctor_get(v_snd_797_, 1);
lean_inc(v_rangeStartPosCharacter_803_);
v_rangeEndPosLine_804_ = lean_ctor_get(v_snd_797_, 2);
lean_inc(v_rangeEndPosLine_804_);
v_rangeEndPosCharacter_805_ = lean_ctor_get(v_snd_797_, 3);
lean_inc(v_rangeEndPosCharacter_805_);
v_selectionRangeStartPosLine_806_ = lean_ctor_get(v_snd_797_, 4);
lean_inc(v_selectionRangeStartPosLine_806_);
v_selectionRangeStartPosCharacter_807_ = lean_ctor_get(v_snd_797_, 5);
lean_inc(v_selectionRangeStartPosCharacter_807_);
v_selectionRangeEndPosLine_808_ = lean_ctor_get(v_snd_797_, 6);
lean_inc(v_selectionRangeEndPosLine_808_);
v_selectionRangeEndPosCharacter_809_ = lean_ctor_get(v_snd_797_, 7);
lean_inc(v_selectionRangeEndPosCharacter_809_);
lean_dec(v_snd_797_);
v___x_810_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_802_);
v___x_811_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_803_);
v___x_813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
v___x_814_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_804_);
v___x_815_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___x_816_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_805_);
v___x_817_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
v___x_818_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_806_);
v___x_819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_807_);
v___x_821_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_808_);
v___x_823_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_809_);
v___x_825_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(8u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
v___x_828_ = lean_array_push(v___x_827_, v___x_811_);
v___x_829_ = lean_array_push(v___x_828_, v___x_813_);
v___x_830_ = lean_array_push(v___x_829_, v___x_815_);
v___x_831_ = lean_array_push(v___x_830_, v___x_817_);
v___x_832_ = lean_array_push(v___x_831_, v___x_819_);
v___x_833_ = lean_array_push(v___x_832_, v___x_821_);
v___x_834_ = lean_array_push(v___x_833_, v___x_823_);
v___x_835_ = lean_array_push(v___x_834_, v___x_825_);
v___x_836_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_836_);
v___x_838_ = v___x_800_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_fst_798_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_841_, lean_object* v_x2_842_, lean_object* v_x3_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_x1_841_);
lean_ctor_set(v___x_844_, 1, v_x2_842_);
v___x_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_x3_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_846_, lean_object* v___f_847_, lean_object* v_m_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_851_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_850_, v___f_846_, v___x_849_, v_m_848_);
v___x_852_ = l_List_mapTR_loop___redArg(v___f_847_, v___x_851_, v___x_849_);
v___x_853_ = l_Lean_Json_mkObj(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v_x_860_, lean_object* v_y_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_string_dec_lt(v_x_860_, v_y_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = lean_string_dec_eq(v_x_860_, v_y_861_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = 2;
return v___x_864_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = 1;
return v___x_865_;
}
}
else
{
uint8_t v___x_866_; 
v___x_866_ = 0;
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0___boxed(lean_object* v_x_867_, lean_object* v_y_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Lean_Lsp_instFromJsonDecls___lam__0(v_x_867_, v_y_868_);
lean_dec_ref(v_y_868_);
lean_dec_ref(v_x_867_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___f_873_, lean_object* v_m_874_, lean_object* v_k_875_, lean_object* v_v_876_){
_start:
{
if (lean_obj_tag(v_v_876_) == 4)
{
lean_object* v_elems_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_996_; 
v_elems_877_ = lean_ctor_get(v_v_876_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v_v_876_);
if (v_isSharedCheck_996_ == 0)
{
v___x_879_ = v_v_876_;
v_isShared_880_ = v_isSharedCheck_996_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_elems_877_);
lean_dec(v_v_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_996_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_881_ = lean_array_get_size(v_elems_877_);
v___x_882_ = lean_unsigned_to_nat(8u);
v___x_883_ = lean_nat_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v___x_884_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_885_ = l_Nat_reprFast(v___x_881_);
v___x_886_ = lean_string_append(v___x_884_, v___x_885_);
lean_dec_ref(v___x_885_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 0);
lean_ctor_set(v___x_879_, 0, v___x_886_);
v___x_888_ = v___x_879_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_del_object(v___x_879_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_891_);
lean_inc(v___x_892_);
v___x_893_ = l_Lean_Json_getNat_x3f(v___x_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_902_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_893_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_903_);
lean_inc(v___x_904_);
v___x_905_ = l_Lean_Json_getNat_x3f(v___x_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_914_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_905_);
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_915_);
lean_inc(v___x_916_);
v___x_917_ = l_Lean_Json_getNat_x3f(v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_a_926_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_917_);
v___x_927_ = lean_unsigned_to_nat(3u);
v___x_928_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_927_);
lean_inc(v___x_928_);
v___x_929_ = l_Lean_Json_getNat_x3f(v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_926_);
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_938_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_929_);
v___x_939_ = lean_unsigned_to_nat(4u);
v___x_940_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_939_);
lean_inc(v___x_940_);
v___x_941_ = l_Lean_Json_getNat_x3f(v___x_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_938_);
lean_dec(v_a_926_);
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_941_);
v___x_951_ = lean_unsigned_to_nat(5u);
v___x_952_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_951_);
lean_inc(v___x_952_);
v___x_953_ = l_Lean_Json_getNat_x3f(v___x_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_950_);
lean_dec(v_a_938_);
lean_dec(v_a_926_);
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_962_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_953_);
v___x_963_ = lean_unsigned_to_nat(6u);
v___x_964_ = lean_array_get_borrowed(v___x_890_, v_elems_877_, v___x_963_);
lean_inc(v___x_964_);
v___x_965_ = l_Lean_Json_getNat_x3f(v___x_964_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_962_);
lean_dec(v_a_950_);
lean_dec(v_a_938_);
lean_dec(v_a_926_);
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_elems_877_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_a_974_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_965_);
v___x_975_ = lean_unsigned_to_nat(7u);
v___x_976_ = lean_array_get(v___x_890_, v_elems_877_, v___x_975_);
lean_dec_ref(v_elems_877_);
v___x_977_ = l_Lean_Json_getNat_x3f(v___x_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_a_974_);
lean_dec(v_a_962_);
lean_dec(v_a_950_);
lean_dec(v_a_938_);
lean_dec(v_a_926_);
lean_dec(v_a_914_);
lean_dec(v_a_902_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_995_; 
v_a_986_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_995_ == 0)
{
v___x_988_ = v___x_977_;
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_977_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_990_, 0, v_a_902_);
lean_ctor_set(v___x_990_, 1, v_a_914_);
lean_ctor_set(v___x_990_, 2, v_a_926_);
lean_ctor_set(v___x_990_, 3, v_a_938_);
lean_ctor_set(v___x_990_, 4, v_a_950_);
lean_ctor_set(v___x_990_, 5, v_a_962_);
lean_ctor_set(v___x_990_, 6, v_a_974_);
lean_ctor_set(v___x_990_, 7, v_a_986_);
v___x_991_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_873_, v_k_875_, v___x_990_, v_m_874_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
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
lean_object* v___x_997_; 
lean_dec(v_v_876_);
lean_dec_ref(v_k_875_);
lean_dec(v_m_874_);
lean_dec_ref(v___f_873_);
v___x_997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__2(lean_object* v___x_998_, lean_object* v___f_999_, lean_object* v_j_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Json_getObj_x3f(v_j_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v___f_999_);
lean_dec_ref(v___x_998_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1010_);
lean_dec_ref(v___x_1001_);
v___x_1011_ = lean_box(1);
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_998_, v___f_999_, v___x_1011_, v_a_1010_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1044_, lean_object* v_parentDecl_x3f_1045_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1045_) == 0)
{
lean_object* v_start_1046_; lean_object* v_end_1047_; lean_object* v_line_1048_; lean_object* v_character_1049_; lean_object* v_line_1050_; lean_object* v_character_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_start_1046_ = lean_ctor_get(v_range_1044_, 0);
v_end_1047_ = lean_ctor_get(v_range_1044_, 1);
v_line_1048_ = lean_ctor_get(v_start_1046_, 0);
v_character_1049_ = lean_ctor_get(v_start_1046_, 1);
v_line_1050_ = lean_ctor_get(v_end_1047_, 0);
v_character_1051_ = lean_ctor_get(v_end_1047_, 1);
v___x_1052_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1051_);
lean_inc(v_line_1050_);
lean_inc(v_character_1049_);
lean_inc(v_line_1048_);
v___x_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1053_, 0, v_line_1048_);
lean_ctor_set(v___x_1053_, 1, v_character_1049_);
lean_ctor_set(v___x_1053_, 2, v_line_1050_);
lean_ctor_set(v___x_1053_, 3, v_character_1051_);
lean_ctor_set(v___x_1053_, 4, v___x_1052_);
return v___x_1053_;
}
else
{
lean_object* v_start_1054_; lean_object* v_end_1055_; lean_object* v_line_1056_; lean_object* v_character_1057_; lean_object* v_line_1058_; lean_object* v_character_1059_; lean_object* v_val_1060_; lean_object* v___x_1061_; 
v_start_1054_ = lean_ctor_get(v_range_1044_, 0);
v_end_1055_ = lean_ctor_get(v_range_1044_, 1);
v_line_1056_ = lean_ctor_get(v_start_1054_, 0);
v_character_1057_ = lean_ctor_get(v_start_1054_, 1);
v_line_1058_ = lean_ctor_get(v_end_1055_, 0);
v_character_1059_ = lean_ctor_get(v_end_1055_, 1);
v_val_1060_ = lean_ctor_get(v_parentDecl_x3f_1045_, 0);
lean_inc(v_val_1060_);
lean_inc(v_character_1059_);
lean_inc(v_line_1058_);
lean_inc(v_character_1057_);
lean_inc(v_line_1056_);
v___x_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1061_, 0, v_line_1056_);
lean_ctor_set(v___x_1061_, 1, v_character_1057_);
lean_ctor_set(v___x_1061_, 2, v_line_1058_);
lean_ctor_set(v___x_1061_, 3, v_character_1059_);
lean_ctor_set(v___x_1061_, 4, v_val_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1062_, lean_object* v_parentDecl_x3f_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1062_, v_parentDecl_x3f_1063_);
lean_dec(v_parentDecl_x3f_1063_);
lean_dec_ref(v_range_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1065_){
_start:
{
lean_object* v_startPosLine_1066_; lean_object* v_startPosCharacter_1067_; lean_object* v_endPosLine_1068_; lean_object* v_endPosCharacter_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_startPosLine_1066_ = lean_ctor_get(v_l_1065_, 0);
v_startPosCharacter_1067_ = lean_ctor_get(v_l_1065_, 1);
v_endPosLine_1068_ = lean_ctor_get(v_l_1065_, 2);
v_endPosCharacter_1069_ = lean_ctor_get(v_l_1065_, 3);
lean_inc(v_startPosCharacter_1067_);
lean_inc(v_startPosLine_1066_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_startPosLine_1066_);
lean_ctor_set(v___x_1070_, 1, v_startPosCharacter_1067_);
lean_inc(v_endPosCharacter_1069_);
lean_inc(v_endPosLine_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_endPosLine_1068_);
lean_ctor_set(v___x_1071_, 1, v_endPosCharacter_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1073_);
lean_dec_ref(v_l_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1075_){
_start:
{
lean_object* v_parentDecl_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_parentDecl_1076_ = lean_ctor_get(v_l_1075_, 4);
v___x_1077_ = lean_string_utf8_byte_size(v_parentDecl_1076_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_nat_dec_eq(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_inc_ref(v_parentDecl_1076_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_parentDecl_1076_);
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1082_);
lean_dec_ref(v_l_1082_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = l_Lean_JsonNumber_fromNat(v_n_1084_);
v___x_1086_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1087_, lean_object* v_l_1088_){
_start:
{
lean_object* v_startPosLine_1089_; lean_object* v_startPosCharacter_1090_; lean_object* v_endPosLine_1091_; lean_object* v_endPosCharacter_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_range_1098_; lean_object* v___x_1099_; 
v_startPosLine_1089_ = lean_ctor_get(v_l_1088_, 0);
v_startPosCharacter_1090_ = lean_ctor_get(v_l_1088_, 1);
v_endPosLine_1091_ = lean_ctor_get(v_l_1088_, 2);
v_endPosCharacter_1092_ = lean_ctor_get(v_l_1088_, 3);
v___x_1093_ = lean_box(0);
lean_inc(v_endPosCharacter_1092_);
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_endPosCharacter_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_inc(v_endPosLine_1091_);
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_endPosLine_1091_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
lean_inc(v_startPosCharacter_1090_);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_startPosCharacter_1090_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_inc(v_startPosLine_1089_);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_startPosLine_1089_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v_range_1098_ = l_List_mapTR_loop___redArg(v___f_1087_, v___x_1097_, v___x_1093_);
v___x_1099_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1088_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = l_List_appendTR___redArg(v_range_1098_, v___x_1093_);
return v___x_1100_;
}
else
{
lean_object* v_val_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v_val_1101_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v___x_1099_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_val_1101_);
lean_dec(v___x_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 3);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1101_);
v___x_1106_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1093_);
v___x_1108_ = l_List_appendTR___redArg(v_range_1098_, v___x_1107_);
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1111_, lean_object* v_l_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1111_, v_l_1112_);
lean_dec_ref(v_l_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_1(v_locationToList_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1119_, lean_object* v___f_1120_, lean_object* v_locationToList_1121_, lean_object* v_i_1122_){
_start:
{
lean_object* v_definition_x3f_1123_; lean_object* v_usages_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1156_; 
v_definition_x3f_1123_ = lean_ctor_get(v_i_1122_, 0);
v_usages_1124_ = lean_ctor_get(v_i_1122_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_i_1122_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1126_ = v_i_1122_;
v_isShared_1127_ = v_isSharedCheck_1156_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_usages_1124_);
lean_inc(v_definition_x3f_1123_);
lean_dec(v_i_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1156_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___y_1130_; 
v___x_1128_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1123_) == 0)
{
lean_object* v___x_1146_; 
lean_dec_ref(v_locationToList_1121_);
v___x_1146_ = lean_box(0);
v___y_1130_ = v___x_1146_;
goto v___jp_1129_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_val_1147_ = lean_ctor_get(v_definition_x3f_1123_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_definition_x3f_1123_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v_definition_x3f_1123_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v_definition_x3f_1123_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_apply_1(v_locationToList_1121_, v_val_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
v___y_1130_ = v___x_1153_;
goto v___jp_1129_;
}
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
lean_inc_ref(v___x_1119_);
v___x_1131_ = l_Option_toJson___redArg(v___x_1119_, v___y_1130_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1131_);
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1133_ = v___x_1126_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1134_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1136_ = lean_array_size(v_usages_1124_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1120_, v_sz_1136_, v___x_1137_, v_usages_1124_);
v___x_1139_ = l_Array_toJson___redArg(v___x_1119_, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1134_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1133_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_Json_mkObj(v___x_1143_);
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1253_; 
v___x_1172_ = lean_array_get_size(v_a_1171_);
v___x_1173_ = lean_unsigned_to_nat(4u);
v___x_1253_ = lean_nat_dec_eq(v___x_1172_, v___x_1173_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(5u);
v___x_1255_ = lean_nat_dec_eq(v___x_1172_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1257_ = l_Nat_reprFast(v___x_1172_);
v___x_1258_ = lean_string_append(v___x_1256_, v___x_1257_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
else
{
goto v___jp_1174_;
}
}
else
{
goto v___jp_1174_;
}
v___jp_1174_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_array_fget_borrowed(v_a_1171_, v___x_1175_);
lean_inc(v___x_1176_);
v___x_1177_ = l_Lean_Json_getNat_x3f(v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_a_1186_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1177_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_array_fget_borrowed(v_a_1171_, v___x_1187_);
lean_inc(v___x_1188_);
v___x_1189_ = l_Lean_Json_getNat_x3f(v___x_1188_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_a_1186_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1198_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1189_);
v___x_1199_ = lean_unsigned_to_nat(2u);
v___x_1200_ = lean_array_fget_borrowed(v_a_1171_, v___x_1199_);
lean_inc(v___x_1200_);
v___x_1201_ = l_Lean_Json_getNat_x3f(v___x_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_a_1198_);
lean_dec(v_a_1186_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1201_);
v___x_1211_ = lean_unsigned_to_nat(3u);
v___x_1212_ = lean_array_fget_borrowed(v_a_1171_, v___x_1211_);
lean_inc(v___x_1212_);
v___x_1213_ = l_Lean_Json_getNat_x3f(v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1210_);
lean_dec(v_a_1198_);
lean_dec(v_a_1186_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1252_; 
v_a_1222_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1224_ = v___x_1213_;
v_isShared_1225_ = v_isSharedCheck_1252_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1213_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1252_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(5u);
v___x_1227_ = lean_nat_dec_eq(v___x_1172_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1228_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1186_);
lean_ctor_set(v___x_1229_, 1, v_a_1198_);
lean_ctor_set(v___x_1229_, 2, v_a_1210_);
lean_ctor_set(v___x_1229_, 3, v_a_1222_);
lean_ctor_set(v___x_1229_, 4, v___x_1228_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1229_);
v___x_1231_ = v___x_1224_;
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
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_del_object(v___x_1224_);
v___x_1233_ = lean_array_fget_borrowed(v_a_1171_, v___x_1173_);
lean_inc(v___x_1233_);
v___x_1234_ = l_Lean_Json_getStr_x3f(v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_a_1222_);
lean_dec(v_a_1210_);
lean_dec(v_a_1198_);
lean_dec(v_a_1186_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
v_a_1243_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v___x_1234_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1234_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1186_);
lean_ctor_set(v___x_1247_, 1, v_a_1198_);
lean_ctor_set(v___x_1247_, 2, v_a_1210_);
lean_ctor_set(v___x_1247_, 3, v_a_1222_);
lean_ctor_set(v___x_1247_, 4, v_a_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1260_);
lean_dec_ref(v_a_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, lean_object* v_toLocation_1265_, lean_object* v_j_1266_){
_start:
{
lean_object* v_definition_x3f_1268_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1266_);
v___x_1301_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1266_, v___x_1262_, v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_j_1266_);
lean_dec_ref(v_toLocation_1265_);
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1301_);
if (lean_obj_tag(v_a_1310_) == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_box(0);
v_definition_x3f_1268_ = v___x_1311_;
goto v___jp_1267_;
}
else
{
lean_object* v_val_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1329_; 
v_val_1312_ = lean_ctor_get(v_a_1310_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1314_ = v_a_1310_;
v_isShared_1315_ = v_isSharedCheck_1329_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_val_1312_);
lean_dec(v_a_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1329_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; 
lean_inc_ref(v_toLocation_1265_);
v___x_1316_ = lean_apply_1(v_toLocation_1265_, v_val_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1314_);
lean_dec(v_j_1266_);
lean_dec_ref(v_toLocation_1265_);
lean_dec_ref(v___x_1264_);
lean_dec_ref(v___x_1263_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1316_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_a_1325_);
v___x_1327_ = v___x_1314_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
v_definition_x3f_1268_ = v___x_1327_;
goto v___jp_1267_;
}
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1270_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1266_, v___x_1263_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_definition_x3f_1268_);
lean_dec_ref(v_toLocation_1265_);
lean_dec_ref(v___x_1264_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1279_; size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v_a_1279_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1270_);
v_sz_1280_ = lean_array_size(v_a_1279_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1264_, v_toLocation_1265_, v_sz_1280_, v___x_1281_, v_a_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_definition_x3f_1268_);
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
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_definition_x3f_1268_);
lean_ctor_set(v___x_1295_, 1, v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
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
lean_object* v___x_1344_; 
v___x_1344_ = lean_box(1);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_box(1);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1346_, lean_object* v_a_1347_, lean_object* v_b_1348_, lean_object* v_c_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1347_);
lean_ctor_set(v___x_1350_, 1, v_b_1348_);
v___x_1351_ = lean_apply_2(v_f_1346_, v___x_1350_, v_c_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1352_, lean_object* v_____do__lift_1353_){
_start:
{
lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1354_ = lean_ctor_get(v_____do__lift_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v_____do__lift_1353_);
v___x_1355_ = lean_apply_2(v_toPure_1352_, lean_box(0), v_a_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_map_1358_, lean_object* v_init_1359_, lean_object* v_f_1360_){
_start:
{
lean_object* v_toApplicative_1361_; lean_object* v_toBind_1362_; lean_object* v_toPure_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; 
v_toApplicative_1361_ = lean_ctor_get(v_inst_1356_, 0);
v_toBind_1362_ = lean_ctor_get(v_inst_1356_, 1);
lean_inc(v_toBind_1362_);
v_toPure_1363_ = lean_ctor_get(v_toApplicative_1361_, 1);
lean_inc(v_toPure_1363_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1364_, 0, v_f_1360_);
v___x_1365_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1356_, v___f_1364_, v_init_1359_, v_map_1358_);
v___f_1366_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1366_, 0, v_toPure_1363_);
v___x_1367_ = lean_apply_4(v_toBind_1362_, lean_box(0), lean_box(0), v___x_1365_, v___f_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1368_){
_start:
{
lean_object* v___f_1369_; 
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1369_, 0, v_inst_1368_);
return v___f_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v_startPosLine_1375_; lean_object* v_startPosCharacter_1376_; lean_object* v_endPosLine_1377_; lean_object* v_endPosCharacter_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_range_1384_; lean_object* v___x_1385_; 
v_startPosLine_1375_ = lean_ctor_get(v_x_1374_, 0);
v_startPosCharacter_1376_ = lean_ctor_get(v_x_1374_, 1);
v_endPosLine_1377_ = lean_ctor_get(v_x_1374_, 2);
v_endPosCharacter_1378_ = lean_ctor_get(v_x_1374_, 3);
v___x_1379_ = lean_box(0);
lean_inc(v_endPosCharacter_1378_);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_endPosCharacter_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_inc(v_endPosLine_1377_);
v___x_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_endPosLine_1377_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
lean_inc(v_startPosCharacter_1376_);
v___x_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_startPosCharacter_1376_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_inc(v_startPosLine_1375_);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_startPosLine_1375_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v_range_1384_ = l_List_mapTR_loop___redArg(v___f_1373_, v___x_1383_, v___x_1379_);
v___x_1385_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1374_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = l_List_appendTR___redArg(v_range_1384_, v___x_1379_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1396_; 
v_val_1387_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1389_ = v___x_1385_;
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1385_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 3);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_val_1387_);
v___x_1392_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1379_);
v___x_1394_ = l_List_appendTR___redArg(v_range_1384_, v___x_1393_);
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1397_, v_x_1398_);
lean_dec_ref(v_x_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1400_, lean_object* v___f_1401_, lean_object* v_x_1402_){
_start:
{
lean_object* v_snd_1403_; lean_object* v_fst_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1465_; 
v_snd_1403_ = lean_ctor_get(v_x_1402_, 1);
v_fst_1404_ = lean_ctor_get(v_x_1402_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1402_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1406_ = v_x_1402_;
v_isShared_1407_ = v_isSharedCheck_1465_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1403_);
lean_inc(v_fst_1404_);
lean_dec(v_x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1465_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_definition_x3f_1408_; lean_object* v_usages_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1464_; 
v_definition_x3f_1408_ = lean_ctor_get(v_snd_1403_, 0);
v_usages_1409_ = lean_ctor_get(v_snd_1403_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_snd_1403_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1411_ = v_snd_1403_;
v_isShared_1412_ = v_isSharedCheck_1464_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_usages_1409_);
lean_inc(v_definition_x3f_1408_);
lean_dec(v_snd_1403_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1464_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___y_1418_; lean_object* v___y_1438_; 
v___x_1413_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1404_);
v___x_1414_ = l_Lean_Json_compress(v___x_1413_);
v___x_1415_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1416_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1408_) == 0)
{
lean_object* v___x_1440_; 
lean_dec_ref(v___f_1401_);
v___x_1440_ = lean_box(0);
v___y_1418_ = v___x_1440_;
goto v___jp_1417_;
}
else
{
lean_object* v_val_1441_; lean_object* v_startPosLine_1442_; lean_object* v_startPosCharacter_1443_; lean_object* v_endPosLine_1444_; lean_object* v_endPosCharacter_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_range_1451_; lean_object* v___x_1452_; 
v_val_1441_ = lean_ctor_get(v_definition_x3f_1408_, 0);
lean_inc(v_val_1441_);
lean_dec_ref(v_definition_x3f_1408_);
v_startPosLine_1442_ = lean_ctor_get(v_val_1441_, 0);
v_startPosCharacter_1443_ = lean_ctor_get(v_val_1441_, 1);
v_endPosLine_1444_ = lean_ctor_get(v_val_1441_, 2);
v_endPosCharacter_1445_ = lean_ctor_get(v_val_1441_, 3);
v___x_1446_ = lean_box(0);
lean_inc(v_endPosCharacter_1445_);
v___x_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_endPosCharacter_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
lean_inc(v_endPosLine_1444_);
v___x_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_endPosLine_1444_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_inc(v_startPosCharacter_1443_);
v___x_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_startPosCharacter_1443_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
lean_inc(v_startPosLine_1442_);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_startPosLine_1442_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v_range_1451_ = l_List_mapTR_loop___redArg(v___f_1401_, v___x_1450_, v___x_1446_);
v___x_1452_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1441_);
lean_dec(v_val_1441_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = l_List_appendTR___redArg(v_range_1451_, v___x_1446_);
v___y_1438_ = v___x_1453_;
goto v___jp_1437_;
}
else
{
lean_object* v_val_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1463_; 
v_val_1454_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_val_1454_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 3);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_val_1454_);
v___x_1459_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1446_);
v___x_1461_ = l_List_appendTR___redArg(v_range_1451_, v___x_1460_);
v___y_1438_ = v___x_1461_;
goto v___jp_1437_;
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = l_Option_toJson___redArg(v___x_1415_, v___y_1418_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1419_);
lean_ctor_set(v___x_1406_, 0, v___x_1416_);
v___x_1421_ = v___x_1406_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; size_t v_sz_1424_; size_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1422_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1423_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1424_ = lean_array_size(v_usages_1409_);
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1423_, v___f_1400_, v_sz_1424_, v___x_1425_, v_usages_1409_);
v___x_1427_ = l_Array_toJson___redArg(v___x_1415_, v___x_1426_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v___x_1427_);
lean_ctor_set(v___x_1411_, 0, v___x_1422_);
v___x_1429_ = v___x_1411_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1421_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_Json_mkObj(v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1414_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
return v___x_1434_;
}
}
}
v___jp_1437_:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1438_);
v___y_1418_ = v___x_1439_;
goto v___jp_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1466_, lean_object* v_x2_1467_, lean_object* v_x3_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_x1_1466_);
lean_ctor_set(v___x_1469_, 1, v_x2_1467_);
v___x_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_x3_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1471_, lean_object* v___f_1472_, lean_object* v_m_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1475_, v___f_1471_, v___x_1474_, v_m_1473_);
v___x_1477_ = l_List_mapTR_loop___redArg(v___f_1472_, v___x_1476_, v___x_1474_);
v___x_1478_ = l_Lean_Json_mkObj(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1489_, lean_object* v_m_1490_, lean_object* v_k_1491_, lean_object* v_v_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Json_parse(v_k_1491_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
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
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1502_);
lean_dec_ref(v___x_1493_);
v___x_1503_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_a_1512_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1503_);
v___x_1513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__11));
v___x_1514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1515_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1492_);
v___x_1516_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1492_, v___x_1514_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
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
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1646_; 
v_a_1525_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1527_ = v___x_1516_;
v_isShared_1528_ = v_isSharedCheck_1646_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1516_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1646_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_definition_x3f_1531_; lean_object* v_a_1566_; 
v___x_1529_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1525_) == 0)
{
lean_object* v___x_1568_; 
lean_del_object(v___x_1527_);
v___x_1568_ = lean_box(0);
v_definition_x3f_1531_ = v___x_1568_;
goto v___jp_1530_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1637_; 
v_val_1569_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v_a_1525_);
v___x_1570_ = lean_array_get_size(v_val_1569_);
v___x_1571_ = lean_unsigned_to_nat(4u);
v___x_1637_ = lean_nat_dec_eq(v___x_1570_, v___x_1571_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_unsigned_to_nat(5u);
v___x_1639_ = lean_nat_dec_eq(v___x_1570_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec(v_val_1569_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v___x_1640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1641_ = l_Nat_reprFast(v___x_1570_);
v___x_1642_ = lean_string_append(v___x_1640_, v___x_1641_);
lean_dec_ref(v___x_1641_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1642_);
v___x_1644_ = v___x_1527_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
else
{
lean_del_object(v___x_1527_);
goto v___jp_1572_;
}
}
else
{
lean_del_object(v___x_1527_);
goto v___jp_1572_;
}
v___jp_1572_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_array_fget_borrowed(v_val_1569_, v___x_1573_);
lean_inc(v___x_1574_);
v___x_1575_ = l_Lean_Json_getNat_x3f(v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_val_1569_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1584_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1575_);
v___x_1585_ = lean_unsigned_to_nat(1u);
v___x_1586_ = lean_array_fget_borrowed(v_val_1569_, v___x_1585_);
lean_inc(v___x_1586_);
v___x_1587_ = l_Lean_Json_getNat_x3f(v___x_1586_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1584_);
lean_dec(v_val_1569_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1596_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1587_);
v___x_1597_ = lean_unsigned_to_nat(2u);
v___x_1598_ = lean_array_fget_borrowed(v_val_1569_, v___x_1597_);
lean_inc(v___x_1598_);
v___x_1599_ = l_Lean_Json_getNat_x3f(v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1596_);
lean_dec(v_a_1584_);
lean_dec(v_val_1569_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
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
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1599_);
v___x_1609_ = lean_unsigned_to_nat(3u);
v___x_1610_ = lean_array_fget_borrowed(v_val_1569_, v___x_1609_);
lean_inc(v___x_1610_);
v___x_1611_ = l_Lean_Json_getNat_x3f(v___x_1610_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1608_);
lean_dec(v_a_1596_);
lean_dec(v_a_1584_);
lean_dec(v_val_1569_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_a_1620_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1620_);
lean_dec_ref(v___x_1611_);
v___x_1621_ = lean_unsigned_to_nat(5u);
v___x_1622_ = lean_nat_dec_eq(v___x_1570_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v_val_1569_);
v___x_1623_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1584_);
lean_ctor_set(v___x_1624_, 1, v_a_1596_);
lean_ctor_set(v___x_1624_, 2, v_a_1608_);
lean_ctor_set(v___x_1624_, 3, v_a_1620_);
lean_ctor_set(v___x_1624_, 4, v___x_1623_);
v_a_1566_ = v___x_1624_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_array_fget(v_val_1569_, v___x_1571_);
lean_dec(v_val_1569_);
v___x_1626_ = l_Lean_Json_getStr_x3f(v___x_1625_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1620_);
lean_dec(v_a_1608_);
lean_dec(v_a_1596_);
lean_dec(v_a_1584_);
lean_dec(v_a_1512_);
lean_dec(v_v_1492_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1626_);
v___x_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1636_, 0, v_a_1584_);
lean_ctor_set(v___x_1636_, 1, v_a_1596_);
lean_ctor_set(v___x_1636_, 2, v_a_1608_);
lean_ctor_set(v___x_1636_, 3, v_a_1620_);
lean_ctor_set(v___x_1636_, 4, v_a_1635_);
v_a_1566_ = v___x_1636_;
goto v___jp_1565_;
}
}
}
}
}
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1533_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1492_, v___x_1529_, v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_definition_x3f_1531_);
lean_dec(v_a_1512_);
lean_dec(v_m_1490_);
lean_dec_ref(v_toLocation_1489_);
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
lean_object* v_a_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1533_);
v_sz_1543_ = lean_array_size(v_a_1542_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1513_, v_toLocation_1489_, v_sz_1543_, v___x_1544_, v_a_1542_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_definition_x3f_1531_);
lean_dec(v_a_1512_);
lean_dec(v_m_1490_);
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
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1564_; 
v_a_1554_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1556_ = v___x_1545_;
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1545_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_definition_x3f_1531_);
lean_ctor_set(v___x_1558_, 1, v_a_1554_);
v___x_1559_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1560_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1559_, v_a_1512_, v___x_1558_, v_m_1490_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1560_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
v___jp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1566_);
v_definition_x3f_1531_ = v___x_1567_;
goto v___jp_1530_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1647_, lean_object* v___f_1648_, lean_object* v_j_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Json_getObj_x3f(v_j_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v___f_1648_);
lean_dec_ref(v___x_1647_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1650_);
v___x_1660_ = lean_box(1);
v___x_1661_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1647_, v___f_1648_, v___x_1660_, v_a_1659_);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1668_, lean_object* v_k_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = l_Lean_Json_getObjValD(v_j_1668_, v_k_1669_);
v___x_1671_ = l_Lean_Json_getNat_x3f(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1672_, v_k_1673_);
lean_dec_ref(v_k_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1675_, lean_object* v_k_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Lean_Json_getObjValD(v_j_1675_, v_k_1676_);
v___x_1678_ = l_Lean_Json_getBool_x3f(v___x_1677_);
lean_dec(v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1679_, lean_object* v_k_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1679_, v_k_1680_);
lean_dec_ref(v_k_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_bs_1686_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_bs_1686_);
return v___x_1690_;
}
else
{
lean_object* v_v_1691_; 
v_v_1691_ = lean_array_uget_borrowed(v_bs_1686_, v_i_1685_);
if (lean_obj_tag(v_v_1691_) == 4)
{
lean_object* v_elems_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_elems_1692_ = lean_ctor_get(v_v_1691_, 0);
v___x_1693_ = lean_array_get_size(v_elems_1692_);
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = lean_nat_dec_eq(v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v_bs_1686_);
goto v___jp_1687_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_array_fget_borrowed(v_elems_1692_, v___x_1696_);
lean_inc(v___x_1697_);
v___x_1698_ = l_Lean_Json_getStr_x3f(v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v_bs_1686_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_a_1707_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1698_);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_array_fget_borrowed(v_elems_1692_, v___x_1708_);
v___x_1710_ = l_Lean_Json_getBool_x3f(v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1707_);
lean_dec_ref(v_bs_1686_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1719_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1710_);
v___x_1720_ = lean_unsigned_to_nat(2u);
v___x_1721_ = lean_array_fget_borrowed(v_elems_1692_, v___x_1720_);
v___x_1722_ = l_Lean_Json_getBool_x3f(v___x_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_a_1719_);
lean_dec(v_a_1707_);
lean_dec_ref(v_bs_1686_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1722_);
v___x_1732_ = lean_unsigned_to_nat(3u);
v___x_1733_ = lean_array_fget_borrowed(v_elems_1692_, v___x_1732_);
v___x_1734_ = l_Lean_Json_getBool_x3f(v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1731_);
lean_dec(v_a_1719_);
lean_dec(v_a_1707_);
lean_dec_ref(v_bs_1686_);
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v_bs_x27_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1734_);
v_bs_x27_1744_ = lean_array_uset(v_bs_1686_, v_i_1685_, v___x_1696_);
v___x_1745_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1745_, 0, v_a_1707_);
v___x_1746_ = lean_unbox(v_a_1719_);
lean_dec(v_a_1719_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*1, v___x_1746_);
v___x_1747_ = lean_unbox(v_a_1731_);
lean_dec(v_a_1731_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*1 + 1, v___x_1747_);
v___x_1748_ = lean_unbox(v_a_1743_);
lean_dec(v_a_1743_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*1 + 2, v___x_1748_);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1685_, v___x_1749_);
v___x_1751_ = lean_array_uset(v_bs_x27_1744_, v_i_1685_, v___x_1745_);
v_i_1685_ = v___x_1750_;
v_bs_1686_ = v___x_1751_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1686_);
goto v___jp_1687_;
}
}
v___jp_1687_:
{
lean_object* v___x_1688_; 
v___x_1688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1756_, v_i_boxed_1757_, v_bs_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1761_){
_start:
{
if (lean_obj_tag(v_x_1761_) == 4)
{
lean_object* v_elems_1762_; size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v_elems_1762_ = lean_ctor_get(v_x_1761_, 0);
lean_inc_ref(v_elems_1762_);
lean_dec_ref(v_x_1761_);
v_sz_1763_ = lean_array_size(v_elems_1762_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1763_, v___x_1764_, v_elems_1762_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1766_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1767_ = lean_unsigned_to_nat(80u);
v___x_1768_ = l_Lean_Json_pretty(v_x_1761_, v___x_1767_);
v___x_1769_ = lean_string_append(v___x_1766_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1773_, lean_object* v_k_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = l_Lean_Json_getObjValD(v_j_1773_, v_k_1774_);
v___x_1776_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1777_, lean_object* v_k_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1777_, v_k_1778_);
lean_dec_ref(v_k_1778_);
return v_res_1779_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = 1;
v___x_1789_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1794_ = lean_string_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = 1;
v___x_1798_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1801_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1805_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1806_ = lean_string_append(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = 1;
v___x_1811_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1812_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1815_ = lean_string_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1818_ = lean_string_append(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = 1;
v___x_1823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1824_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1827_ = lean_string_append(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1829_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1830_ = lean_string_append(v___x_1829_, v___x_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1831_);
v___x_1833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1831_, v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_json_1831_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1839_ = lean_string_append(v___x_1838_, v_a_1834_);
lean_dec(v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_json_1831_);
v_a_1844_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1833_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1833_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 0);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_a_1852_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1833_);
v___x_1853_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1831_);
v___x_1854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1831_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1852_);
lean_dec(v_json_1831_);
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1860_ = lean_string_append(v___x_1859_, v_a_1855_);
lean_dec(v_a_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1860_);
v___x_1862_ = v___x_1857_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_a_1852_);
lean_dec(v_json_1831_);
v_a_1865_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1854_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1854_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 0);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_a_1873_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1854_);
v___x_1874_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1875_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1831_, v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1852_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1881_ = lean_string_append(v___x_1880_, v_a_1876_);
lean_dec(v_a_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1852_);
v_a_1886_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1875_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1875_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 0);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1903_; 
v_a_1894_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1896_ = v___x_1875_;
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1875_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1898_, 0, v_a_1852_);
lean_ctor_set(v___x_1898_, 1, v_a_1894_);
v___x_1899_ = lean_unbox(v_a_1873_);
lean_dec(v_a_1873_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*2, v___x_1899_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1901_ = v___x_1896_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1898_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1906_, size_t v_i_1907_, lean_object* v_bs_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
if (v___x_1909_ == 0)
{
return v_bs_1908_;
}
else
{
lean_object* v_v_1910_; lean_object* v_module_1911_; uint8_t v_isPrivate_1912_; uint8_t v_isAll_1913_; uint8_t v_isMeta_1914_; lean_object* v___x_1915_; lean_object* v_bs_x27_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v_v_1910_ = lean_array_uget_borrowed(v_bs_1908_, v_i_1907_);
v_module_1911_ = lean_ctor_get(v_v_1910_, 0);
lean_inc_ref(v_module_1911_);
v_isPrivate_1912_ = lean_ctor_get_uint8(v_v_1910_, sizeof(void*)*1);
v_isAll_1913_ = lean_ctor_get_uint8(v_v_1910_, sizeof(void*)*1 + 1);
v_isMeta_1914_ = lean_ctor_get_uint8(v_v_1910_, sizeof(void*)*1 + 2);
v___x_1915_ = lean_unsigned_to_nat(0u);
v_bs_x27_1916_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_module_1911_);
v___x_1918_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1918_, 0, v_isPrivate_1912_);
v___x_1919_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1919_, 0, v_isAll_1913_);
v___x_1920_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1920_, 0, v_isMeta_1914_);
v___x_1921_ = lean_unsigned_to_nat(4u);
v___x_1922_ = lean_mk_empty_array_with_capacity(v___x_1921_);
v___x_1923_ = lean_array_push(v___x_1922_, v___x_1917_);
v___x_1924_ = lean_array_push(v___x_1923_, v___x_1918_);
v___x_1925_ = lean_array_push(v___x_1924_, v___x_1919_);
v___x_1926_ = lean_array_push(v___x_1925_, v___x_1920_);
v___x_1927_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_add(v_i_1907_, v___x_1928_);
v___x_1930_ = lean_array_uset(v_bs_x27_1916_, v_i_1907_, v___x_1927_);
v_i_1907_ = v___x_1929_;
v_bs_1908_ = v___x_1930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1932_, lean_object* v_i_1933_, lean_object* v_bs_1934_){
_start:
{
size_t v_sz_boxed_1935_; size_t v_i_boxed_1936_; lean_object* v_res_1937_; 
v_sz_boxed_1935_ = lean_unbox_usize(v_sz_1932_);
lean_dec(v_sz_1932_);
v_i_boxed_1936_ = lean_unbox_usize(v_i_1933_);
lean_dec(v_i_1933_);
v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1935_, v_i_boxed_1936_, v_bs_1934_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1938_){
_start:
{
size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_sz_1939_ = lean_array_size(v_a_1938_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1939_, v___x_1940_, v_a_1938_);
v___x_1942_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
if (lean_obj_tag(v_a_1943_) == 0)
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_array_to_list(v_a_1944_);
return v___x_1945_;
}
else
{
lean_object* v_head_1946_; lean_object* v_tail_1947_; lean_object* v___x_1948_; 
v_head_1946_ = lean_ctor_get(v_a_1943_, 0);
lean_inc(v_head_1946_);
v_tail_1947_ = lean_ctor_get(v_a_1943_, 1);
lean_inc(v_tail_1947_);
lean_dec_ref(v_a_1943_);
v___x_1948_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1944_, v_head_1946_);
v_a_1943_ = v_tail_1947_;
v_a_1944_ = v___x_1948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1952_){
_start:
{
lean_object* v_version_1953_; uint8_t v_isSetupFailure_1954_; lean_object* v_directImports_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_version_1953_ = lean_ctor_get(v_x_1952_, 0);
lean_inc(v_version_1953_);
v_isSetupFailure_1954_ = lean_ctor_get_uint8(v_x_1952_, sizeof(void*)*2);
v_directImports_1955_ = lean_ctor_get(v_x_1952_, 1);
lean_inc_ref(v_directImports_1955_);
lean_dec_ref(v_x_1952_);
v___x_1956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1957_ = l_Lean_JsonNumber_fromNat(v_version_1953_);
v___x_1958_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1956_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1963_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1963_, 0, v_isSetupFailure_1954_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v___x_1960_);
v___x_1966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1967_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1955_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___x_1960_);
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1960_);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1965_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1961_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1974_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1972_, v___x_1973_);
v___x_1975_ = l_Lean_Json_mkObj(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1978_, lean_object* v_v_1979_, lean_object* v_t_1980_){
_start:
{
if (lean_obj_tag(v_t_1980_) == 0)
{
lean_object* v_size_1981_; lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2266_; 
v_size_1981_ = lean_ctor_get(v_t_1980_, 0);
v_k_1982_ = lean_ctor_get(v_t_1980_, 1);
v_v_1983_ = lean_ctor_get(v_t_1980_, 2);
v_l_1984_ = lean_ctor_get(v_t_1980_, 3);
v_r_1985_ = lean_ctor_get(v_t_1980_, 4);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_t_1980_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_1987_ = v_t_1980_;
v_isShared_1988_ = v_isSharedCheck_2266_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_r_1985_);
lean_inc(v_l_1984_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
lean_inc(v_size_1981_);
lean_dec(v_t_1980_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2266_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_string_dec_lt(v_k_1978_, v_k_1982_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_string_dec_eq(v_k_1978_, v_k_1982_);
if (v___x_1990_ == 0)
{
lean_object* v_impl_1991_; lean_object* v___x_1992_; 
lean_dec(v_size_1981_);
v_impl_1991_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1978_, v_v_1979_, v_r_1985_);
v___x_1992_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1984_) == 0)
{
lean_object* v_size_1993_; lean_object* v_size_1994_; lean_object* v_k_1995_; lean_object* v_v_1996_; lean_object* v_l_1997_; lean_object* v_r_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_size_1993_ = lean_ctor_get(v_l_1984_, 0);
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
v___x_2002_ = lean_nat_add(v___x_1992_, v_size_1993_);
v___x_2003_ = lean_nat_add(v___x_2002_, v_size_1994_);
lean_dec(v_size_1994_);
lean_dec(v___x_2002_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_impl_1991_);
lean_ctor_set(v___x_1987_, 0, v___x_2003_);
v___x_2005_ = v___x_1987_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_l_1984_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_impl_1991_);
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
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2070_; 
v_isSharedCheck_2070_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2071_ = lean_ctor_get(v_impl_1991_, 4);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_impl_1991_, 2);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_impl_1991_, 1);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2075_);
v___x_2008_ = v_impl_1991_;
v_isShared_2009_ = v_isSharedCheck_2070_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_impl_1991_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2070_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_size_2010_; lean_object* v_k_2011_; lean_object* v_v_2012_; lean_object* v_l_2013_; lean_object* v_r_2014_; lean_object* v_size_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_size_2010_ = lean_ctor_get(v_l_1997_, 0);
v_k_2011_ = lean_ctor_get(v_l_1997_, 1);
v_v_2012_ = lean_ctor_get(v_l_1997_, 2);
v_l_2013_ = lean_ctor_get(v_l_1997_, 3);
v_r_2014_ = lean_ctor_get(v_l_1997_, 4);
v_size_2015_ = lean_ctor_get(v_r_1998_, 0);
v___x_2016_ = lean_unsigned_to_nat(2u);
v___x_2017_ = lean_nat_mul(v___x_2016_, v_size_2015_);
v___x_2018_ = lean_nat_dec_lt(v_size_2010_, v___x_2017_);
lean_dec(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2046_; 
lean_inc(v_r_2014_);
lean_inc(v_l_2013_);
lean_inc(v_v_2012_);
lean_inc(v_k_2011_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_l_1997_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; 
v_unused_2047_ = lean_ctor_get(v_l_1997_, 4);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_l_1997_, 3);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_l_1997_, 2);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_l_1997_, 1);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_l_1997_, 0);
lean_dec(v_unused_2051_);
v___x_2020_ = v_l_1997_;
v_isShared_2021_ = v_isSharedCheck_2046_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v_l_1997_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2046_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2036_; 
v___x_2022_ = lean_nat_add(v___x_1992_, v_size_1993_);
v___x_2023_ = lean_nat_add(v___x_2022_, v_size_1994_);
lean_dec(v_size_1994_);
if (lean_obj_tag(v_l_2013_) == 0)
{
lean_object* v_size_2044_; 
v_size_2044_ = lean_ctor_get(v_l_2013_, 0);
lean_inc(v_size_2044_);
v___y_2036_ = v_size_2044_;
goto v___jp_2035_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___y_2036_ = v___x_2045_;
goto v___jp_2035_;
}
v___jp_2024_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_nat_add(v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 4, v_r_1998_);
lean_ctor_set(v___x_2020_, 3, v_r_2014_);
lean_ctor_set(v___x_2020_, 2, v_v_1996_);
lean_ctor_set(v___x_2020_, 1, v_k_1995_);
lean_ctor_set(v___x_2020_, 0, v___x_2028_);
v___x_2030_ = v___x_2020_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_r_2014_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_r_1998_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2030_);
lean_ctor_set(v___x_2008_, 3, v___y_2025_);
lean_ctor_set(v___x_2008_, 2, v_v_2012_);
lean_ctor_set(v___x_2008_, 1, v_k_2011_);
lean_ctor_set(v___x_2008_, 0, v___x_2023_);
v___x_2032_ = v___x_2008_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_2011_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_2012_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___y_2025_);
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
v___jp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_nat_add(v___x_2022_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec(v___x_2022_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_l_2013_);
lean_ctor_set(v___x_1987_, 0, v___x_2037_);
v___x_2039_ = v___x_1987_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_l_1984_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v_l_2013_);
v___x_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_nat_add(v___x_1992_, v_size_2015_);
if (lean_obj_tag(v_r_2014_) == 0)
{
lean_object* v_size_2041_; 
v_size_2041_ = lean_ctor_get(v_r_2014_, 0);
lean_inc(v_size_2041_);
v___y_2025_ = v___x_2039_;
v___y_2026_ = v___x_2040_;
v___y_2027_ = v_size_2041_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v___y_2025_ = v___x_2039_;
v___y_2026_ = v___x_2040_;
v___y_2027_ = v___x_2042_;
goto v___jp_2024_;
}
}
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_del_object(v___x_1987_);
v___x_2052_ = lean_nat_add(v___x_1992_, v_size_1993_);
v___x_2053_ = lean_nat_add(v___x_2052_, v_size_1994_);
lean_dec(v_size_1994_);
v___x_2054_ = lean_nat_add(v___x_2052_, v_size_2010_);
lean_dec(v___x_2052_);
lean_inc_ref(v_l_1984_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_l_1997_);
lean_ctor_set(v___x_2008_, 3, v_l_1984_);
lean_ctor_set(v___x_2008_, 2, v_v_1983_);
lean_ctor_set(v___x_2008_, 1, v_k_1982_);
lean_ctor_set(v___x_2008_, 0, v___x_2054_);
v___x_2056_ = v___x_2008_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_l_1984_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_l_1997_);
v___x_2056_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_isSharedCheck_2063_ = !lean_is_exclusive(v_l_1984_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; lean_object* v_unused_2068_; 
v_unused_2064_ = lean_ctor_get(v_l_1984_, 4);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_l_1984_, 3);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_l_1984_, 2);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_l_1984_, 1);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_l_1984_, 0);
lean_dec(v_unused_2068_);
v___x_2058_ = v_l_1984_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v_l_1984_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 4, v_r_1998_);
lean_ctor_set(v___x_2058_, 3, v___x_2056_);
lean_ctor_set(v___x_2058_, 2, v_v_1996_);
lean_ctor_set(v___x_2058_, 1, v_k_1995_);
lean_ctor_set(v___x_2058_, 0, v___x_2053_);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_r_1998_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2076_; 
v_l_2076_ = lean_ctor_get(v_impl_1991_, 3);
lean_inc(v_l_2076_);
if (lean_obj_tag(v_l_2076_) == 0)
{
lean_object* v_r_2077_; lean_object* v_k_2078_; lean_object* v_v_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2102_; 
v_r_2077_ = lean_ctor_get(v_impl_1991_, 4);
v_k_2078_ = lean_ctor_get(v_impl_1991_, 1);
v_v_2079_ = lean_ctor_get(v_impl_1991_, 2);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; lean_object* v_unused_2104_; 
v_unused_2103_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2104_);
v___x_2081_ = v_impl_1991_;
v_isShared_2082_ = v_isSharedCheck_2102_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_r_2077_);
lean_inc(v_v_2079_);
lean_inc(v_k_2078_);
lean_dec(v_impl_1991_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2102_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_k_2083_; lean_object* v_v_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_k_2083_ = lean_ctor_get(v_l_2076_, 1);
v_v_2084_ = lean_ctor_get(v_l_2076_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_l_2076_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; lean_object* v_unused_2100_; lean_object* v_unused_2101_; 
v_unused_2099_ = lean_ctor_get(v_l_2076_, 4);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_l_2076_, 3);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_l_2076_, 0);
lean_dec(v_unused_2101_);
v___x_2086_ = v_l_2076_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_v_2084_);
lean_inc(v_k_2083_);
lean_dec(v_l_2076_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2077_, 2);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 4, v_r_2077_);
lean_ctor_set(v___x_2086_, 3, v_r_2077_);
lean_ctor_set(v___x_2086_, 2, v_v_1983_);
lean_ctor_set(v___x_2086_, 1, v_k_1982_);
lean_ctor_set(v___x_2086_, 0, v___x_1992_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_r_2077_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_r_2077_);
v___x_2090_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
lean_inc(v_r_2077_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 3, v_r_2077_);
lean_ctor_set(v___x_2081_, 0, v___x_1992_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2078_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2079_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_r_2077_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_r_2077_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v___x_2092_);
lean_ctor_set(v___x_1987_, 3, v___x_2090_);
lean_ctor_set(v___x_1987_, 2, v_v_2084_);
lean_ctor_set(v___x_1987_, 1, v_k_2083_);
lean_ctor_set(v___x_1987_, 0, v___x_2088_);
v___x_2094_ = v___x_1987_;
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
lean_object* v_r_2105_; 
v_r_2105_ = lean_ctor_get(v_impl_1991_, 4);
lean_inc(v_r_2105_);
if (lean_obj_tag(v_r_2105_) == 0)
{
lean_object* v_k_2106_; lean_object* v_v_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2118_; 
v_k_2106_ = lean_ctor_get(v_impl_1991_, 1);
v_v_2107_ = lean_ctor_get(v_impl_1991_, 2);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_impl_1991_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; lean_object* v_unused_2120_; lean_object* v_unused_2121_; 
v_unused_2119_ = lean_ctor_get(v_impl_1991_, 4);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_impl_1991_, 3);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_impl_1991_, 0);
lean_dec(v_unused_2121_);
v___x_2109_ = v_impl_1991_;
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_v_2107_);
lean_inc(v_k_2106_);
lean_dec(v_impl_1991_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2118_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_unsigned_to_nat(3u);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 4, v_l_2076_);
lean_ctor_set(v___x_2109_, 2, v_v_1983_);
lean_ctor_set(v___x_2109_, 1, v_k_1982_);
lean_ctor_set(v___x_2109_, 0, v___x_1992_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_l_2076_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_l_2076_);
v___x_2113_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2115_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_r_2105_);
lean_ctor_set(v___x_1987_, 3, v___x_2113_);
lean_ctor_set(v___x_1987_, 2, v_v_2107_);
lean_ctor_set(v___x_1987_, 1, v_k_2106_);
lean_ctor_set(v___x_1987_, 0, v___x_2111_);
v___x_2115_ = v___x_1987_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2106_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2107_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_r_2105_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_unsigned_to_nat(2u);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_impl_1991_);
lean_ctor_set(v___x_1987_, 3, v_r_2105_);
lean_ctor_set(v___x_1987_, 0, v___x_2122_);
v___x_2124_ = v___x_1987_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_r_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_impl_1991_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_v_1983_);
lean_dec(v_k_1982_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 2, v_v_1979_);
lean_ctor_set(v___x_1987_, 1, v_k_1978_);
v___x_2127_ = v___x_1987_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_size_1981_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_1978_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_1979_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_l_1984_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_r_1985_);
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
lean_object* v_impl_2129_; lean_object* v___x_2130_; 
lean_dec(v_size_1981_);
v_impl_2129_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1978_, v_v_1979_, v_l_1984_);
v___x_2130_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1985_) == 0)
{
lean_object* v_size_2131_; lean_object* v_size_2132_; lean_object* v_k_2133_; lean_object* v_v_2134_; lean_object* v_l_2135_; lean_object* v_r_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_size_2131_ = lean_ctor_get(v_r_1985_, 0);
v_size_2132_ = lean_ctor_get(v_impl_2129_, 0);
lean_inc(v_size_2132_);
v_k_2133_ = lean_ctor_get(v_impl_2129_, 1);
lean_inc(v_k_2133_);
v_v_2134_ = lean_ctor_get(v_impl_2129_, 2);
lean_inc(v_v_2134_);
v_l_2135_ = lean_ctor_get(v_impl_2129_, 3);
lean_inc(v_l_2135_);
v_r_2136_ = lean_ctor_get(v_impl_2129_, 4);
lean_inc(v_r_2136_);
v___x_2137_ = lean_unsigned_to_nat(3u);
v___x_2138_ = lean_nat_mul(v___x_2137_, v_size_2131_);
v___x_2139_ = lean_nat_dec_lt(v___x_2138_, v_size_2132_);
lean_dec(v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec(v_r_2136_);
lean_dec(v_l_2135_);
lean_dec(v_v_2134_);
lean_dec(v_k_2133_);
v___x_2140_ = lean_nat_add(v___x_2130_, v_size_2132_);
lean_dec(v_size_2132_);
v___x_2141_ = lean_nat_add(v___x_2140_, v_size_2131_);
lean_dec(v___x_2140_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 3, v_impl_2129_);
lean_ctor_set(v___x_1987_, 0, v___x_2141_);
v___x_2143_ = v___x_1987_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_impl_2129_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_r_1985_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v_impl_2129_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2211_ = lean_ctor_get(v_impl_2129_, 4);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_impl_2129_, 3);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_impl_2129_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_impl_2129_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_impl_2129_, 0);
lean_dec(v_unused_2215_);
v___x_2146_ = v_impl_2129_;
v_isShared_2147_ = v_isSharedCheck_2210_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v_impl_2129_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2210_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_size_2148_; lean_object* v_size_2149_; lean_object* v_k_2150_; lean_object* v_v_2151_; lean_object* v_l_2152_; lean_object* v_r_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_size_2148_ = lean_ctor_get(v_l_2135_, 0);
v_size_2149_ = lean_ctor_get(v_r_2136_, 0);
v_k_2150_ = lean_ctor_get(v_r_2136_, 1);
v_v_2151_ = lean_ctor_get(v_r_2136_, 2);
v_l_2152_ = lean_ctor_get(v_r_2136_, 3);
v_r_2153_ = lean_ctor_get(v_r_2136_, 4);
v___x_2154_ = lean_unsigned_to_nat(2u);
v___x_2155_ = lean_nat_mul(v___x_2154_, v_size_2148_);
v___x_2156_ = lean_nat_dec_lt(v_size_2149_, v___x_2155_);
lean_dec(v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2185_; 
lean_inc(v_r_2153_);
lean_inc(v_l_2152_);
lean_inc(v_v_2151_);
lean_inc(v_k_2150_);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_r_2136_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2186_ = lean_ctor_get(v_r_2136_, 4);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_r_2136_, 3);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_r_2136_, 2);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_r_2136_, 1);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_r_2136_, 0);
lean_dec(v_unused_2190_);
v___x_2158_ = v_r_2136_;
v_isShared_2159_ = v_isSharedCheck_2185_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v_r_2136_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2185_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___x_2173_; lean_object* v___y_2175_; 
v___x_2160_ = lean_nat_add(v___x_2130_, v_size_2132_);
lean_dec(v_size_2132_);
v___x_2161_ = lean_nat_add(v___x_2160_, v_size_2131_);
lean_dec(v___x_2160_);
v___x_2173_ = lean_nat_add(v___x_2130_, v_size_2148_);
if (lean_obj_tag(v_l_2152_) == 0)
{
lean_object* v_size_2183_; 
v_size_2183_ = lean_ctor_get(v_l_2152_, 0);
lean_inc(v_size_2183_);
v___y_2175_ = v_size_2183_;
goto v___jp_2174_;
}
else
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___y_2175_ = v___x_2184_;
goto v___jp_2174_;
}
v___jp_2162_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_nat_add(v___y_2163_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec(v___y_2163_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 4, v_r_1985_);
lean_ctor_set(v___x_2158_, 3, v_r_2153_);
lean_ctor_set(v___x_2158_, 2, v_v_1983_);
lean_ctor_set(v___x_2158_, 1, v_k_1982_);
lean_ctor_set(v___x_2158_, 0, v___x_2166_);
v___x_2168_ = v___x_2158_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_2153_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_r_1985_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v___x_2168_);
lean_ctor_set(v___x_2146_, 3, v___y_2164_);
lean_ctor_set(v___x_2146_, 2, v_v_2151_);
lean_ctor_set(v___x_2146_, 1, v_k_2150_);
lean_ctor_set(v___x_2146_, 0, v___x_2161_);
v___x_2170_ = v___x_2146_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2150_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2151_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v___y_2164_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
v___jp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = lean_nat_add(v___x_2173_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec(v___x_2173_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_l_2152_);
lean_ctor_set(v___x_1987_, 3, v_l_2135_);
lean_ctor_set(v___x_1987_, 2, v_v_2134_);
lean_ctor_set(v___x_1987_, 1, v_k_2133_);
lean_ctor_set(v___x_1987_, 0, v___x_2176_);
v___x_2178_ = v___x_1987_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_k_2133_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_v_2134_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_l_2135_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v_l_2152_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_nat_add(v___x_2130_, v_size_2131_);
if (lean_obj_tag(v_r_2153_) == 0)
{
lean_object* v_size_2180_; 
v_size_2180_ = lean_ctor_get(v_r_2153_, 0);
lean_inc(v_size_2180_);
v___y_2163_ = v___x_2179_;
v___y_2164_ = v___x_2178_;
v___y_2165_ = v_size_2180_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___y_2163_ = v___x_2179_;
v___y_2164_ = v___x_2178_;
v___y_2165_ = v___x_2181_;
goto v___jp_2162_;
}
}
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_del_object(v___x_1987_);
v___x_2191_ = lean_nat_add(v___x_2130_, v_size_2132_);
lean_dec(v_size_2132_);
v___x_2192_ = lean_nat_add(v___x_2191_, v_size_2131_);
lean_dec(v___x_2191_);
v___x_2193_ = lean_nat_add(v___x_2130_, v_size_2131_);
v___x_2194_ = lean_nat_add(v___x_2193_, v_size_2149_);
lean_dec(v___x_2193_);
lean_inc_ref(v_r_1985_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_r_1985_);
lean_ctor_set(v___x_2146_, 3, v_r_2136_);
lean_ctor_set(v___x_2146_, 2, v_v_1983_);
lean_ctor_set(v___x_2146_, 1, v_k_1982_);
lean_ctor_set(v___x_2146_, 0, v___x_2194_);
v___x_2196_ = v___x_2146_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_r_2136_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_r_1985_);
v___x_2196_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v_r_1985_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2204_ = lean_ctor_get(v_r_1985_, 4);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_r_1985_, 3);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_r_1985_, 2);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_r_1985_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_r_1985_, 0);
lean_dec(v_unused_2208_);
v___x_2198_ = v_r_1985_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_r_1985_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v___x_2196_);
lean_ctor_set(v___x_2198_, 3, v_l_2135_);
lean_ctor_set(v___x_2198_, 2, v_v_2134_);
lean_ctor_set(v___x_2198_, 1, v_k_2133_);
lean_ctor_set(v___x_2198_, 0, v___x_2192_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2133_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2134_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_l_2135_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v___x_2196_);
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
v_l_2216_ = lean_ctor_get(v_impl_2129_, 3);
lean_inc(v_l_2216_);
if (lean_obj_tag(v_l_2216_) == 0)
{
lean_object* v_r_2217_; lean_object* v_k_2218_; lean_object* v_v_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
v_r_2217_ = lean_ctor_get(v_impl_2129_, 4);
v_k_2218_ = lean_ctor_get(v_impl_2129_, 1);
v_v_2219_ = lean_ctor_get(v_impl_2129_, 2);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_impl_2129_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2231_ = lean_ctor_get(v_impl_2129_, 3);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_impl_2129_, 0);
lean_dec(v_unused_2232_);
v___x_2221_ = v_impl_2129_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_r_2217_);
lean_inc(v_v_2219_);
lean_inc(v_k_2218_);
lean_dec(v_impl_2129_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2217_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v_r_2217_);
lean_ctor_set(v___x_2221_, 2, v_v_1983_);
lean_ctor_set(v___x_2221_, 1, v_k_1982_);
lean_ctor_set(v___x_2221_, 0, v___x_2130_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_r_2217_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_r_2217_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v___x_2225_);
lean_ctor_set(v___x_1987_, 3, v_l_2216_);
lean_ctor_set(v___x_1987_, 2, v_v_2219_);
lean_ctor_set(v___x_1987_, 1, v_k_2218_);
lean_ctor_set(v___x_1987_, 0, v___x_2223_);
v___x_2227_ = v___x_1987_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2218_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2219_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_r_2233_; 
v_r_2233_ = lean_ctor_get(v_impl_2129_, 4);
lean_inc(v_r_2233_);
if (lean_obj_tag(v_r_2233_) == 0)
{
lean_object* v_k_2234_; lean_object* v_v_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2258_; 
v_k_2234_ = lean_ctor_get(v_impl_2129_, 1);
v_v_2235_ = lean_ctor_get(v_impl_2129_, 2);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_impl_2129_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; lean_object* v_unused_2260_; lean_object* v_unused_2261_; 
v_unused_2259_ = lean_ctor_get(v_impl_2129_, 4);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_impl_2129_, 3);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2129_, 0);
lean_dec(v_unused_2261_);
v___x_2237_ = v_impl_2129_;
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_v_2235_);
lean_inc(v_k_2234_);
lean_dec(v_impl_2129_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2254_; 
v_k_2239_ = lean_ctor_get(v_r_2233_, 1);
v_v_2240_ = lean_ctor_get(v_r_2233_, 2);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_r_2233_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2255_ = lean_ctor_get(v_r_2233_, 4);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_r_2233_, 3);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_r_2233_, 0);
lean_dec(v_unused_2257_);
v___x_2242_ = v_r_2233_;
v_isShared_2243_ = v_isSharedCheck_2254_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_v_2240_);
lean_inc(v_k_2239_);
lean_dec(v_r_2233_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2254_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = lean_unsigned_to_nat(3u);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 4, v_l_2216_);
lean_ctor_set(v___x_2242_, 3, v_l_2216_);
lean_ctor_set(v___x_2242_, 2, v_v_2235_);
lean_ctor_set(v___x_2242_, 1, v_k_2234_);
lean_ctor_set(v___x_2242_, 0, v___x_2130_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_l_2216_);
v___x_2246_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v_l_2216_);
lean_ctor_set(v___x_2237_, 2, v_v_1983_);
lean_ctor_set(v___x_2237_, 1, v_k_1982_);
lean_ctor_set(v___x_2237_, 0, v___x_2130_);
v___x_2248_ = v___x_2237_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_l_2216_);
v___x_2248_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v___x_2248_);
lean_ctor_set(v___x_1987_, 3, v___x_2246_);
lean_ctor_set(v___x_1987_, 2, v_v_2240_);
lean_ctor_set(v___x_1987_, 1, v_k_2239_);
lean_ctor_set(v___x_1987_, 0, v___x_2244_);
v___x_2250_ = v___x_1987_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unsigned_to_nat(2u);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v_r_2233_);
lean_ctor_set(v___x_1987_, 3, v_impl_2129_);
lean_ctor_set(v___x_1987_, 0, v___x_2262_);
v___x_2264_ = v___x_1987_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_impl_2129_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_r_2233_);
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
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_k_1978_);
lean_ctor_set(v___x_2268_, 2, v_v_1979_);
lean_ctor_set(v___x_2268_, 3, v_t_1980_);
lean_ctor_set(v___x_2268_, 4, v_t_1980_);
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
lean_dec_ref(v_x_2270_);
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
lean_dec_ref(v_v_2272_);
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
lean_dec_ref(v___x_2293_);
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
lean_dec_ref(v___x_2305_);
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
lean_dec_ref(v___x_2317_);
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
lean_dec_ref(v___x_2329_);
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
lean_dec_ref(v___x_2341_);
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
lean_dec_ref(v___x_2353_);
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
lean_dec_ref(v___x_2365_);
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
lean_dec_ref(v___x_2377_);
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
lean_dec_ref(v___x_2275_);
lean_dec(v_r_2274_);
lean_dec(v_v_2272_);
lean_dec(v_k_2271_);
v___x_2391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
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
lean_dec_ref(v___x_2396_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2411_, size_t v_i_2412_, lean_object* v_bs_2413_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2423_, lean_object* v_i_2424_, lean_object* v_bs_2425_){
_start:
{
size_t v_sz_boxed_2426_; size_t v_i_boxed_2427_; lean_object* v_res_2428_; 
v_sz_boxed_2426_ = lean_unbox_usize(v_sz_2423_);
lean_dec(v_sz_2423_);
v_i_boxed_2427_ = lean_unbox_usize(v_i_2424_);
lean_dec(v_i_2424_);
v_res_2428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2426_, v_i_boxed_2427_, v_bs_2425_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 4)
{
lean_object* v_elems_2430_; size_t v_sz_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v_elems_2430_ = lean_ctor_get(v_x_2429_, 0);
lean_inc_ref(v_elems_2430_);
lean_dec_ref(v_x_2429_);
v_sz_2431_ = lean_array_size(v_elems_2430_);
v___x_2432_ = ((size_t)0ULL);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2431_, v___x_2432_, v_elems_2430_);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2434_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2435_ = lean_unsigned_to_nat(80u);
v___x_2436_ = l_Lean_Json_pretty(v_x_2429_, v___x_2435_);
v___x_2437_ = lean_string_append(v___x_2434_, v___x_2436_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2439_ = lean_string_append(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2443_);
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
v___x_2466_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2465_);
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
lean_object* v_v_2765_; lean_object* v___x_2766_; lean_object* v_bs_x27_2767_; lean_object* v_a_2769_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2840_; 
v_v_2765_ = lean_array_uget(v_bs_2762_, v_i_2761_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v_bs_x27_2767_ = lean_array_uset(v_bs_2762_, v_i_2761_, v___x_2766_);
v___x_2774_ = lean_array_get_size(v_v_2765_);
v___x_2775_ = lean_unsigned_to_nat(4u);
v___x_2840_ = lean_nat_dec_eq(v___x_2774_, v___x_2775_);
if (v___x_2840_ == 0)
{
if (v___x_2763_ == 0)
{
goto v___jp_2776_;
}
else
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = lean_unsigned_to_nat(5u);
v___x_2842_ = lean_nat_dec_eq(v___x_2774_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v___x_2843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2844_ = l_Nat_reprFast(v___x_2774_);
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
else
{
goto v___jp_2776_;
}
}
}
else
{
goto v___jp_2776_;
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
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_array_fget_borrowed(v_v_2765_, v___x_2766_);
lean_inc(v___x_2777_);
v___x_2778_ = l_Lean_Json_getNat_x3f(v___x_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2787_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2778_);
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_array_fget_borrowed(v_v_2765_, v___x_2788_);
lean_inc(v___x_2789_);
v___x_2790_ = l_Lean_Json_getNat_x3f(v___x_2789_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2787_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2799_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2790_);
v___x_2800_ = lean_unsigned_to_nat(2u);
v___x_2801_ = lean_array_fget_borrowed(v_v_2765_, v___x_2800_);
lean_inc(v___x_2801_);
v___x_2802_ = l_Lean_Json_getNat_x3f(v___x_2801_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2799_);
lean_dec(v_a_2787_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
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
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2811_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2802_);
v___x_2812_ = lean_unsigned_to_nat(3u);
v___x_2813_ = lean_array_fget_borrowed(v_v_2765_, v___x_2812_);
lean_inc(v___x_2813_);
v___x_2814_ = l_Lean_Json_getNat_x3f(v___x_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v_a_2811_);
lean_dec(v_a_2799_);
lean_dec(v_a_2787_);
lean_dec_ref(v_bs_x27_2767_);
lean_dec(v_v_2765_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v_a_2823_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2814_);
v___x_2824_ = lean_unsigned_to_nat(5u);
v___x_2825_ = lean_nat_dec_eq(v___x_2774_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec(v_v_2765_);
v___x_2826_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2787_);
lean_ctor_set(v___x_2827_, 1, v_a_2799_);
lean_ctor_set(v___x_2827_, 2, v_a_2811_);
lean_ctor_set(v___x_2827_, 3, v_a_2823_);
lean_ctor_set(v___x_2827_, 4, v___x_2826_);
v_a_2769_ = v___x_2827_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_array_fget(v_v_2765_, v___x_2775_);
lean_dec(v_v_2765_);
v___x_2829_ = l_Lean_Json_getStr_x3f(v___x_2828_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2811_);
lean_dec(v_a_2799_);
lean_dec(v_a_2787_);
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
lean_dec_ref(v___x_2829_);
v___x_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2787_);
lean_ctor_set(v___x_2839_, 1, v_a_2799_);
lean_ctor_set(v___x_2839_, 2, v_a_2811_);
lean_ctor_set(v___x_2839_, 3, v_a_2823_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2847_, lean_object* v_i_2848_, lean_object* v_bs_2849_){
_start:
{
size_t v_sz_boxed_2850_; size_t v_i_boxed_2851_; lean_object* v_res_2852_; 
v_sz_boxed_2850_ = lean_unbox_usize(v_sz_2847_);
lean_dec(v_sz_2847_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2848_);
lean_dec(v_i_2848_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2850_, v_i_boxed_2851_, v_bs_2849_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2853_, size_t v_i_2854_, lean_object* v_bs_2855_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_lt(v_i_2854_, v_sz_2853_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_bs_2855_);
return v___x_2857_;
}
else
{
lean_object* v_v_2858_; lean_object* v___x_2859_; 
v_v_2858_ = lean_array_uget_borrowed(v_bs_2855_, v_i_2854_);
lean_inc(v_v_2858_);
v___x_2859_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2858_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_bs_2855_);
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v_bs_x27_2870_; size_t v___x_2871_; size_t v___x_2872_; lean_object* v___x_2873_; 
v_a_2868_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2859_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v_bs_x27_2870_ = lean_array_uset(v_bs_2855_, v_i_2854_, v___x_2869_);
v___x_2871_ = ((size_t)1ULL);
v___x_2872_ = lean_usize_add(v_i_2854_, v___x_2871_);
v___x_2873_ = lean_array_uset(v_bs_x27_2870_, v_i_2854_, v_a_2868_);
v_i_2854_ = v___x_2872_;
v_bs_2855_ = v___x_2873_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2875_, lean_object* v_i_2876_, lean_object* v_bs_2877_){
_start:
{
size_t v_sz_boxed_2878_; size_t v_i_boxed_2879_; lean_object* v_res_2880_; 
v_sz_boxed_2878_ = lean_unbox_usize(v_sz_2875_);
lean_dec(v_sz_2875_);
v_i_boxed_2879_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2878_, v_i_boxed_2879_, v_bs_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2881_){
_start:
{
if (lean_obj_tag(v_x_2881_) == 4)
{
lean_object* v_elems_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v_elems_2882_ = lean_ctor_get(v_x_2881_, 0);
lean_inc_ref(v_elems_2882_);
lean_dec_ref(v_x_2881_);
v_sz_2883_ = lean_array_size(v_elems_2882_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2883_, v___x_2884_, v_elems_2882_);
return v___x_2885_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2886_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2887_ = lean_unsigned_to_nat(80u);
v___x_2888_ = l_Lean_Json_pretty(v_x_2881_, v___x_2887_);
v___x_2889_ = lean_string_append(v___x_2886_, v___x_2888_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2893_, lean_object* v_k_2894_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = l_Lean_Json_getObjValD(v_j_2893_, v_k_2894_);
v___x_2896_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2897_, lean_object* v_k_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2897_, v_k_2898_);
lean_dec_ref(v_k_2898_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2900_, lean_object* v_x_2901_){
_start:
{
if (lean_obj_tag(v_x_2901_) == 0)
{
lean_object* v_k_2902_; lean_object* v_v_2903_; lean_object* v_l_2904_; lean_object* v_r_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_3065_; 
v_k_2902_ = lean_ctor_get(v_x_2901_, 1);
v_v_2903_ = lean_ctor_get(v_x_2901_, 2);
v_l_2904_ = lean_ctor_get(v_x_2901_, 3);
v_r_2905_ = lean_ctor_get(v_x_2901_, 4);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_x_2901_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v_x_2901_, 0);
lean_dec(v_unused_3066_);
v___x_2907_ = v_x_2901_;
v_isShared_2908_ = v_isSharedCheck_3065_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_r_2905_);
lean_inc(v_l_2904_);
lean_inc(v_v_2903_);
lean_inc(v_k_2902_);
lean_dec(v_x_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_3065_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2900_, v_l_2904_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
lean_dec(v_k_2902_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_3064_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_3064_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_3064_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Json_parse(v_k_2902_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2914_);
v___x_2924_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v_definition_x3f_2935_; lean_object* v_a_2963_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2933_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2924_);
v___x_2967_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2903_);
v___x_2968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2903_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
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
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3063_; 
v_a_2977_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_2979_ = v___x_2968_;
v_isShared_2980_ = v_isSharedCheck_3063_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2968_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3063_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
if (lean_obj_tag(v_a_2977_) == 0)
{
lean_object* v___x_2981_; 
lean_del_object(v___x_2979_);
lean_del_object(v___x_2912_);
lean_del_object(v___x_2907_);
v___x_2981_ = lean_box(0);
v_definition_x3f_2935_ = v___x_2981_;
goto v___jp_2934_;
}
else
{
lean_object* v_val_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_3054_; 
v_val_2982_ = lean_ctor_get(v_a_2977_, 0);
lean_inc(v_val_2982_);
lean_dec_ref(v_a_2977_);
v___x_2983_ = lean_array_get_size(v_val_2982_);
v___x_2984_ = lean_unsigned_to_nat(4u);
v___x_3054_ = lean_nat_dec_eq(v___x_2983_, v___x_2984_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = lean_unsigned_to_nat(5u);
v___x_3056_ = lean_nat_dec_eq(v___x_2983_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_dec(v_val_2982_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v___x_3057_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3058_ = l_Nat_reprFast(v___x_2983_);
v___x_3059_ = lean_string_append(v___x_3057_, v___x_3058_);
lean_dec_ref(v___x_3058_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 0);
lean_ctor_set(v___x_2979_, 0, v___x_3059_);
v___x_3061_ = v___x_2979_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
lean_del_object(v___x_2979_);
goto v___jp_2985_;
}
}
else
{
lean_del_object(v___x_2979_);
goto v___jp_2985_;
}
v___jp_2985_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = lean_array_fget_borrowed(v_val_2982_, v___x_2986_);
lean_inc(v___x_2987_);
v___x_2988_ = l_Lean_Json_getNat_x3f(v___x_2987_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_val_2982_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_a_2997_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2988_);
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_array_fget_borrowed(v_val_2982_, v___x_2998_);
lean_inc(v___x_2999_);
v___x_3000_ = l_Lean_Json_getNat_x3f(v___x_2999_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_a_2997_);
lean_dec(v_val_2982_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3009_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3000_);
v___x_3010_ = lean_unsigned_to_nat(2u);
v___x_3011_ = lean_array_fget_borrowed(v_val_2982_, v___x_3010_);
lean_inc(v___x_3011_);
v___x_3012_ = l_Lean_Json_getNat_x3f(v___x_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_3009_);
lean_dec(v_a_2997_);
lean_dec(v_val_2982_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3021_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3012_);
v___x_3022_ = lean_unsigned_to_nat(3u);
v___x_3023_ = lean_array_fget_borrowed(v_val_2982_, v___x_3022_);
lean_inc(v___x_3023_);
v___x_3024_ = l_Lean_Json_getNat_x3f(v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_a_3021_);
lean_dec(v_a_3009_);
lean_dec(v_a_2997_);
lean_dec(v_val_2982_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
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
lean_object* v_a_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3024_);
v___x_3034_ = lean_unsigned_to_nat(5u);
v___x_3035_ = lean_nat_dec_eq(v___x_2983_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_dec(v_val_2982_);
v___x_3036_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 4, v___x_3036_);
lean_ctor_set(v___x_2907_, 3, v_a_3033_);
lean_ctor_set(v___x_2907_, 2, v_a_3021_);
lean_ctor_set(v___x_2907_, 1, v_a_3009_);
lean_ctor_set(v___x_2907_, 0, v_a_2997_);
v___x_3038_ = v___x_2907_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_a_3009_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_a_3021_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_a_3033_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
v_a_2963_ = v___x_3038_;
goto v___jp_2962_;
}
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = lean_array_fget(v_val_2982_, v___x_2984_);
lean_dec(v_val_2982_);
v___x_3041_ = l_Lean_Json_getStr_x3f(v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_3033_);
lean_dec(v_a_3021_);
lean_dec(v_a_3009_);
lean_dec(v_a_2997_);
lean_dec(v_a_2933_);
lean_del_object(v___x_2912_);
lean_dec(v_a_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_r_2905_);
lean_dec(v_v_2903_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; 
v_a_3050_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3041_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 4, v_a_3050_);
lean_ctor_set(v___x_2907_, 3, v_a_3033_);
lean_ctor_set(v___x_2907_, 2, v_a_3021_);
lean_ctor_set(v___x_2907_, 1, v_a_3009_);
lean_ctor_set(v___x_2907_, 0, v_a_2997_);
v___x_3052_ = v___x_2907_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_a_3009_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_a_3021_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_a_3033_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_a_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
v_a_2963_ = v___x_3052_;
goto v___jp_2962_;
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
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2937_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2903_, v___x_2936_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_definition_x3f_2935_);
lean_dec(v_a_2933_);
lean_dec(v_a_2910_);
lean_dec(v_r_2905_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
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
lean_object* v_a_2946_; size_t v_sz_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2937_);
v_sz_2947_ = lean_array_size(v_a_2946_);
v___x_2948_ = ((size_t)0ULL);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2947_, v___x_2948_, v_a_2946_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v_definition_x3f_2935_);
lean_dec(v_a_2933_);
lean_dec(v_a_2910_);
lean_dec(v_r_2905_);
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2949_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_definition_x3f_2935_);
lean_ctor_set(v___x_2959_, 1, v_a_2958_);
v___x_2960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2933_, v___x_2959_, v_a_2910_);
v_init_2900_ = v___x_2960_;
v_x_2901_ = v_r_2905_;
goto _start;
}
}
}
v___jp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_a_2963_);
v___x_2965_ = v___x_2912_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v_definition_x3f_2935_ = v___x_2965_;
goto v___jp_2934_;
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
lean_object* v___x_3067_; 
v___x_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_init_2900_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = l_Lean_Json_getObjValD(v_j_3068_, v_k_3069_);
v___x_3071_ = l_Lean_Json_getObj_x3f(v___x_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_a_3080_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3080_);
lean_dec_ref(v___x_3071_);
v___x_3081_ = lean_box(1);
v___x_3082_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3081_, v_a_3080_);
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3083_, lean_object* v_k_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3083_, v_k_3084_);
lean_dec_ref(v_k_3084_);
return v_res_3085_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = 1;
v___x_3092_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3095_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3096_ = lean_string_append(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3099_ = lean_string_append(v___x_3098_, v___x_3097_);
return v___x_3099_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3102_ = lean_string_append(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = 1;
v___x_3107_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3108_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3111_ = lean_string_append(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3114_ = lean_string_append(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = 1;
v___x_3119_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3120_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3123_ = lean_string_append(v___x_3122_, v___x_3121_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3126_ = lean_string_append(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3127_);
v___x_3129_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3127_, v___x_3128_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_json_3127_);
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3139_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3134_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3135_ = lean_string_append(v___x_3134_, v_a_3130_);
lean_dec(v_a_3130_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3135_);
v___x_3137_ = v___x_3132_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_json_3127_);
v_a_3140_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3129_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3129_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_a_3148_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3129_);
v___x_3149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3127_);
v___x_3150_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3127_, v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_a_3148_);
lean_dec(v_json_3127_);
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3160_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3160_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3156_ = lean_string_append(v___x_3155_, v_a_3151_);
lean_dec(v_a_3151_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3156_);
v___x_3158_ = v___x_3153_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_3148_);
lean_dec(v_json_3127_);
v_a_3161_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3150_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3150_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 0);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_a_3169_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3150_);
v___x_3170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3171_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3127_, v___x_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_a_3169_);
lean_dec(v_a_3148_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3177_ = lean_string_append(v___x_3176_, v_a_3172_);
lean_dec(v_a_3172_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3177_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3169_);
lean_dec(v_a_3148_);
v_a_3182_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3171_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3171_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 0);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3198_; 
v_a_3190_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3192_ = v___x_3171_;
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3171_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3198_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3194_, 0, v_a_3148_);
lean_ctor_set(v___x_3194_, 1, v_a_3169_);
lean_ctor_set(v___x_3194_, 2, v_a_3190_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3194_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3199_, lean_object* v_k_3200_, lean_object* v_v_3201_, lean_object* v_t_3202_, lean_object* v_hl_3203_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3200_, v_v_3201_, v_t_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3205_, lean_object* v_k_3206_, lean_object* v_v_3207_, lean_object* v_t_3208_, lean_object* v_hl_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3206_, v_v_3207_, v_t_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_object* v_k_3215_; lean_object* v_v_3216_; lean_object* v_l_3217_; lean_object* v_r_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_k_3215_ = lean_ctor_get(v_x_3214_, 1);
v_v_3216_ = lean_ctor_get(v_x_3214_, 2);
v_l_3217_ = lean_ctor_get(v_x_3214_, 3);
v_r_3218_ = lean_ctor_get(v_x_3214_, 4);
v___x_3219_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3213_, v_r_3218_);
lean_inc(v_v_3216_);
lean_inc(v_k_3215_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_k_3215_);
lean_ctor_set(v___x_3220_, 1, v_v_3216_);
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v___x_3219_);
v_init_3213_ = v___x_3221_;
v_x_3214_ = v_l_3217_;
goto _start;
}
else
{
return v_init_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3223_, lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3223_, v_x_3224_);
lean_dec(v_x_3224_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3226_, size_t v_i_3227_, lean_object* v_bs_3228_){
_start:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_usize_dec_lt(v_i_3227_, v_sz_3226_);
if (v___x_3229_ == 0)
{
return v_bs_3228_;
}
else
{
lean_object* v_v_3230_; lean_object* v___x_3231_; lean_object* v_bs_x27_3232_; size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v_v_3230_ = lean_array_uget(v_bs_3228_, v_i_3227_);
v___x_3231_ = lean_unsigned_to_nat(0u);
v_bs_x27_3232_ = lean_array_uset(v_bs_3228_, v_i_3227_, v___x_3231_);
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_i_3227_, v___x_3233_);
v___x_3235_ = lean_array_uset(v_bs_x27_3232_, v_i_3227_, v_v_3230_);
v_i_3227_ = v___x_3234_;
v_bs_3228_ = v___x_3235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3237_, lean_object* v_i_3238_, lean_object* v_bs_3239_){
_start:
{
size_t v_sz_boxed_3240_; size_t v_i_boxed_3241_; lean_object* v_res_3242_; 
v_sz_boxed_3240_ = lean_unbox_usize(v_sz_3237_);
lean_dec(v_sz_3237_);
v_i_boxed_3241_ = lean_unbox_usize(v_i_3238_);
lean_dec(v_i_3238_);
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3240_, v_i_boxed_3241_, v_bs_3239_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3243_){
_start:
{
size_t v_sz_3244_; size_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_sz_3244_ = lean_array_size(v_a_3243_);
v___x_3245_ = ((size_t)0ULL);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3244_, v___x_3245_, v_a_3243_);
v___x_3247_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3248_){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_array_mk(v_a_3248_);
v___x_3250_ = l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3251_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 0)
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_box(0);
return v___x_3252_;
}
else
{
lean_object* v_val_3253_; lean_object* v___x_3254_; 
v_val_3253_ = lean_ctor_get(v_x_3251_, 0);
lean_inc(v_val_3253_);
lean_dec_ref(v_x_3251_);
v___x_3254_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3253_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3255_, size_t v_i_3256_, lean_object* v_bs_3257_){
_start:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_usize_dec_lt(v_i_3256_, v_sz_3255_);
if (v___x_3258_ == 0)
{
return v_bs_3257_;
}
else
{
lean_object* v_v_3259_; lean_object* v___x_3260_; lean_object* v_bs_x27_3261_; lean_object* v___x_3262_; size_t v___x_3263_; size_t v___x_3264_; lean_object* v___x_3265_; 
v_v_3259_ = lean_array_uget(v_bs_3257_, v_i_3256_);
v___x_3260_ = lean_unsigned_to_nat(0u);
v_bs_x27_3261_ = lean_array_uset(v_bs_3257_, v_i_3256_, v___x_3260_);
v___x_3262_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3259_);
v___x_3263_ = ((size_t)1ULL);
v___x_3264_ = lean_usize_add(v_i_3256_, v___x_3263_);
v___x_3265_ = lean_array_uset(v_bs_x27_3261_, v_i_3256_, v___x_3262_);
v_i_3256_ = v___x_3264_;
v_bs_3257_ = v___x_3265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3267_, lean_object* v_i_3268_, lean_object* v_bs_3269_){
_start:
{
size_t v_sz_boxed_3270_; size_t v_i_boxed_3271_; lean_object* v_res_3272_; 
v_sz_boxed_3270_ = lean_unbox_usize(v_sz_3267_);
lean_dec(v_sz_3267_);
v_i_boxed_3271_ = lean_unbox_usize(v_i_3268_);
lean_dec(v_i_3268_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3270_, v_i_boxed_3271_, v_bs_3269_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3273_){
_start:
{
size_t v_sz_3274_; size_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_sz_3274_ = lean_array_size(v_a_3273_);
v___x_3275_ = ((size_t)0ULL);
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3274_, v___x_3275_, v_a_3273_);
v___x_3277_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
if (lean_obj_tag(v_a_3278_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = l_List_reverse___redArg(v_a_3279_);
return v___x_3280_;
}
else
{
lean_object* v_head_3281_; lean_object* v_tail_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3292_; 
v_head_3281_ = lean_ctor_get(v_a_3278_, 0);
v_tail_3282_ = lean_ctor_get(v_a_3278_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_a_3278_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3284_ = v_a_3278_;
v_isShared_3285_ = v_isSharedCheck_3292_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_tail_3282_);
lean_inc(v_head_3281_);
lean_dec(v_a_3278_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3292_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3286_ = l_Lean_JsonNumber_fromNat(v_head_3281_);
v___x_3287_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v_a_3279_);
lean_ctor_set(v___x_3284_, 0, v___x_3287_);
v___x_3289_ = v___x_3284_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_a_3279_);
v___x_3289_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
v_a_3278_ = v_tail_3282_;
v_a_3279_ = v___x_3289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3293_, size_t v_i_3294_, lean_object* v_bs_3295_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_lt(v_i_3294_, v_sz_3293_);
if (v___x_3296_ == 0)
{
return v_bs_3295_;
}
else
{
lean_object* v_v_3297_; lean_object* v_startPosLine_3298_; lean_object* v_startPosCharacter_3299_; lean_object* v_endPosLine_3300_; lean_object* v_endPosCharacter_3301_; lean_object* v___x_3302_; lean_object* v_bs_x27_3303_; lean_object* v___y_3305_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v_range_3315_; lean_object* v___x_3316_; 
v_v_3297_ = lean_array_uget(v_bs_3295_, v_i_3294_);
v_startPosLine_3298_ = lean_ctor_get(v_v_3297_, 0);
v_startPosCharacter_3299_ = lean_ctor_get(v_v_3297_, 1);
v_endPosLine_3300_ = lean_ctor_get(v_v_3297_, 2);
v_endPosCharacter_3301_ = lean_ctor_get(v_v_3297_, 3);
v___x_3302_ = lean_unsigned_to_nat(0u);
v_bs_x27_3303_ = lean_array_uset(v_bs_3295_, v_i_3294_, v___x_3302_);
v___x_3310_ = lean_box(0);
lean_inc(v_endPosCharacter_3301_);
v___x_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_endPosCharacter_3301_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_inc(v_endPosLine_3300_);
v___x_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3312_, 0, v_endPosLine_3300_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_inc(v_startPosCharacter_3299_);
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_startPosCharacter_3299_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_inc(v_startPosLine_3298_);
v___x_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_startPosLine_3298_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v_range_3315_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3314_, v___x_3310_);
v___x_3316_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3297_);
lean_dec(v_v_3297_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = l_List_appendTR___redArg(v_range_3315_, v___x_3310_);
v___y_3305_ = v___x_3317_;
goto v___jp_3304_;
}
else
{
lean_object* v_val_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3327_; 
v_val_3318_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3320_ = v___x_3316_;
v_isShared_3321_ = v_isSharedCheck_3327_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_val_3318_);
lean_dec(v___x_3316_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3327_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 3);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_val_3318_);
v___x_3323_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3310_);
v___x_3325_ = l_List_appendTR___redArg(v_range_3315_, v___x_3324_);
v___y_3305_ = v___x_3325_;
goto v___jp_3304_;
}
}
}
v___jp_3304_:
{
size_t v___x_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3294_, v___x_3306_);
v___x_3308_ = lean_array_uset(v_bs_x27_3303_, v_i_3294_, v___y_3305_);
v_i_3294_ = v___x_3307_;
v_bs_3295_ = v___x_3308_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3328_, lean_object* v_i_3329_, lean_object* v_bs_3330_){
_start:
{
size_t v_sz_boxed_3331_; size_t v_i_boxed_3332_; lean_object* v_res_3333_; 
v_sz_boxed_3331_ = lean_unbox_usize(v_sz_3328_);
lean_dec(v_sz_3328_);
v_i_boxed_3332_ = lean_unbox_usize(v_i_3329_);
lean_dec(v_i_3329_);
v_res_3333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3331_, v_i_boxed_3332_, v_bs_3330_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
if (lean_obj_tag(v_a_3334_) == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_reverse___redArg(v_a_3335_);
return v___x_3336_;
}
else
{
lean_object* v_head_3337_; lean_object* v_snd_3338_; lean_object* v_tail_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3408_; 
v_head_3337_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_head_3337_);
v_snd_3338_ = lean_ctor_get(v_head_3337_, 1);
lean_inc(v_snd_3338_);
v_tail_3339_ = lean_ctor_get(v_a_3334_, 1);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3334_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_a_3334_, 0);
lean_dec(v_unused_3409_);
v___x_3341_ = v_a_3334_;
v_isShared_3342_ = v_isSharedCheck_3408_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_tail_3339_);
lean_dec(v_a_3334_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3408_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_fst_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3406_; 
v_fst_3343_ = lean_ctor_get(v_head_3337_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_head_3337_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_head_3337_, 1);
lean_dec(v_unused_3407_);
v___x_3345_ = v_head_3337_;
v_isShared_3346_ = v_isSharedCheck_3406_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_fst_3343_);
lean_dec(v_head_3337_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3406_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_definition_x3f_3347_; lean_object* v_usages_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3405_; 
v_definition_x3f_3347_ = lean_ctor_get(v_snd_3338_, 0);
v_usages_3348_ = lean_ctor_get(v_snd_3338_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_snd_3338_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3350_ = v_snd_3338_;
v_isShared_3351_ = v_isSharedCheck_3405_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_usages_3348_);
lean_inc(v_definition_x3f_3347_);
lean_dec(v_snd_3338_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3405_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___y_3356_; lean_object* v___y_3379_; 
v___x_3352_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3343_);
v___x_3353_ = l_Lean_Json_compress(v___x_3352_);
v___x_3354_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3347_) == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_box(0);
v___y_3356_ = v___x_3381_;
goto v___jp_3355_;
}
else
{
lean_object* v_val_3382_; lean_object* v_startPosLine_3383_; lean_object* v_startPosCharacter_3384_; lean_object* v_endPosLine_3385_; lean_object* v_endPosCharacter_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v_range_3392_; lean_object* v___x_3393_; 
v_val_3382_ = lean_ctor_get(v_definition_x3f_3347_, 0);
lean_inc(v_val_3382_);
lean_dec_ref(v_definition_x3f_3347_);
v_startPosLine_3383_ = lean_ctor_get(v_val_3382_, 0);
v_startPosCharacter_3384_ = lean_ctor_get(v_val_3382_, 1);
v_endPosLine_3385_ = lean_ctor_get(v_val_3382_, 2);
v_endPosCharacter_3386_ = lean_ctor_get(v_val_3382_, 3);
v___x_3387_ = lean_box(0);
lean_inc(v_endPosCharacter_3386_);
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_endPosCharacter_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
lean_inc(v_endPosLine_3385_);
v___x_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3389_, 0, v_endPosLine_3385_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_inc(v_startPosCharacter_3384_);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v_startPosCharacter_3384_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
lean_inc(v_startPosLine_3383_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_startPosLine_3383_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v_range_3392_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3391_, v___x_3387_);
v___x_3393_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3382_);
lean_dec(v_val_3382_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = l_List_appendTR___redArg(v_range_3392_, v___x_3387_);
v___y_3379_ = v___x_3394_;
goto v___jp_3378_;
}
else
{
lean_object* v_val_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3404_; 
v_val_3395_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3397_ = v___x_3393_;
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_val_3395_);
lean_dec(v___x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 3);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_val_3395_);
v___x_3400_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3387_);
v___x_3402_ = l_List_appendTR___redArg(v_range_3392_, v___x_3401_);
v___y_3379_ = v___x_3402_;
goto v___jp_3378_;
}
}
}
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3356_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3357_);
lean_ctor_set(v___x_3345_, 0, v___x_3354_);
v___x_3359_ = v___x_3345_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; size_t v_sz_3361_; size_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3360_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3361_ = lean_array_size(v_usages_3348_);
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3361_, v___x_3362_, v_usages_3348_);
v___x_3364_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3363_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 1, v___x_3364_);
lean_ctor_set(v___x_3350_, 0, v___x_3360_);
v___x_3366_ = v___x_3350_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_box(0);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 1, v___x_3367_);
lean_ctor_set(v___x_3341_, 0, v___x_3366_);
v___x_3369_ = v___x_3341_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3359_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = l_Lean_Json_mkObj(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3353_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v_a_3335_);
v_a_3334_ = v_tail_3339_;
v_a_3335_ = v___x_3373_;
goto _start;
}
}
}
}
v___jp_3378_:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___y_3379_);
v___y_3356_ = v___x_3380_;
goto v___jp_3355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
if (lean_obj_tag(v_a_3410_) == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = l_List_reverse___redArg(v_a_3411_);
return v___x_3412_;
}
else
{
lean_object* v_head_3413_; lean_object* v_snd_3414_; lean_object* v_tail_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3467_; 
v_head_3413_ = lean_ctor_get(v_a_3410_, 0);
lean_inc(v_head_3413_);
v_snd_3414_ = lean_ctor_get(v_head_3413_, 1);
lean_inc(v_snd_3414_);
v_tail_3415_ = lean_ctor_get(v_a_3410_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_a_3410_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v_a_3410_, 0);
lean_dec(v_unused_3468_);
v___x_3417_ = v_a_3410_;
v_isShared_3418_ = v_isSharedCheck_3467_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_tail_3415_);
lean_dec(v_a_3410_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3467_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_fst_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3465_; 
v_fst_3419_ = lean_ctor_get(v_head_3413_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_head_3413_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_head_3413_, 1);
lean_dec(v_unused_3466_);
v___x_3421_ = v_head_3413_;
v_isShared_3422_ = v_isSharedCheck_3465_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_fst_3419_);
lean_dec(v_head_3413_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3465_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v_rangeStartPosLine_3423_; lean_object* v_rangeStartPosCharacter_3424_; lean_object* v_rangeEndPosLine_3425_; lean_object* v_rangeEndPosCharacter_3426_; lean_object* v_selectionRangeStartPosLine_3427_; lean_object* v_selectionRangeStartPosCharacter_3428_; lean_object* v_selectionRangeEndPosLine_3429_; lean_object* v_selectionRangeEndPosCharacter_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v_rangeStartPosLine_3423_ = lean_ctor_get(v_snd_3414_, 0);
lean_inc(v_rangeStartPosLine_3423_);
v_rangeStartPosCharacter_3424_ = lean_ctor_get(v_snd_3414_, 1);
lean_inc(v_rangeStartPosCharacter_3424_);
v_rangeEndPosLine_3425_ = lean_ctor_get(v_snd_3414_, 2);
lean_inc(v_rangeEndPosLine_3425_);
v_rangeEndPosCharacter_3426_ = lean_ctor_get(v_snd_3414_, 3);
lean_inc(v_rangeEndPosCharacter_3426_);
v_selectionRangeStartPosLine_3427_ = lean_ctor_get(v_snd_3414_, 4);
lean_inc(v_selectionRangeStartPosLine_3427_);
v_selectionRangeStartPosCharacter_3428_ = lean_ctor_get(v_snd_3414_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3428_);
v_selectionRangeEndPosLine_3429_ = lean_ctor_get(v_snd_3414_, 6);
lean_inc(v_selectionRangeEndPosLine_3429_);
v_selectionRangeEndPosCharacter_3430_ = lean_ctor_get(v_snd_3414_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3430_);
lean_dec(v_snd_3414_);
v___x_3431_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3423_);
v___x_3432_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
v___x_3433_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3424_);
v___x_3434_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3425_);
v___x_3436_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
v___x_3437_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3426_);
v___x_3438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
v___x_3439_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3427_);
v___x_3440_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
v___x_3441_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3428_);
v___x_3442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
v___x_3443_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3429_);
v___x_3444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
v___x_3445_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3430_);
v___x_3446_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
v___x_3447_ = lean_unsigned_to_nat(8u);
v___x_3448_ = lean_mk_empty_array_with_capacity(v___x_3447_);
v___x_3449_ = lean_array_push(v___x_3448_, v___x_3432_);
v___x_3450_ = lean_array_push(v___x_3449_, v___x_3434_);
v___x_3451_ = lean_array_push(v___x_3450_, v___x_3436_);
v___x_3452_ = lean_array_push(v___x_3451_, v___x_3438_);
v___x_3453_ = lean_array_push(v___x_3452_, v___x_3440_);
v___x_3454_ = lean_array_push(v___x_3453_, v___x_3442_);
v___x_3455_ = lean_array_push(v___x_3454_, v___x_3444_);
v___x_3456_ = lean_array_push(v___x_3455_, v___x_3446_);
v___x_3457_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v___x_3457_);
v___x_3459_ = v___x_3421_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3419_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 1, v_a_3411_);
lean_ctor_set(v___x_3417_, 0, v___x_3459_);
v___x_3461_ = v___x_3417_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_a_3411_);
v___x_3461_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v_a_3410_ = v_tail_3415_;
v_a_3411_ = v___x_3461_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3469_, lean_object* v_x_3470_){
_start:
{
if (lean_obj_tag(v_x_3470_) == 0)
{
lean_object* v_k_3471_; lean_object* v_v_3472_; lean_object* v_l_3473_; lean_object* v_r_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_k_3471_ = lean_ctor_get(v_x_3470_, 1);
v_v_3472_ = lean_ctor_get(v_x_3470_, 2);
v_l_3473_ = lean_ctor_get(v_x_3470_, 3);
v_r_3474_ = lean_ctor_get(v_x_3470_, 4);
v___x_3475_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3469_, v_r_3474_);
lean_inc(v_v_3472_);
lean_inc(v_k_3471_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_k_3471_);
lean_ctor_set(v___x_3476_, 1, v_v_3472_);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3475_);
v_init_3469_ = v___x_3477_;
v_x_3470_ = v_l_3473_;
goto _start;
}
else
{
return v_init_3469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3479_, lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3479_, v_x_3480_);
lean_dec(v_x_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3482_){
_start:
{
lean_object* v_version_3483_; lean_object* v_references_3484_; lean_object* v_decls_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_version_3483_ = lean_ctor_get(v_x_3482_, 0);
lean_inc(v_version_3483_);
v_references_3484_ = lean_ctor_get(v_x_3482_, 1);
lean_inc(v_references_3484_);
v_decls_3485_ = lean_ctor_get(v_x_3482_, 2);
lean_inc(v_decls_3485_);
lean_dec_ref(v_x_3482_);
v___x_3486_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3487_ = l_Lean_JsonNumber_fromNat(v_version_3483_);
v___x_3488_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3486_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3493_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3490_, v_references_3484_);
lean_dec(v_references_3484_);
v___x_3494_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3493_, v___x_3490_);
v___x_3495_ = l_Lean_Json_mkObj(v___x_3494_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3492_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
lean_ctor_set(v___x_3497_, 1, v___x_3490_);
v___x_3498_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3499_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3490_, v_decls_3485_);
lean_dec(v_decls_3485_);
v___x_3500_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3499_, v___x_3490_);
v___x_3501_ = l_Lean_Json_mkObj(v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3498_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3490_);
v___x_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___x_3490_);
v___x_3505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3497_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3491_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3508_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3506_, v___x_3507_);
v___x_3509_ = l_Lean_Json_mkObj(v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3512_, size_t v_i_3513_, lean_object* v_bs_3514_){
_start:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_usize_dec_lt(v_i_3513_, v_sz_3512_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_bs_3514_);
return v___x_3516_;
}
else
{
lean_object* v_v_3517_; lean_object* v___x_3518_; 
v_v_3517_ = lean_array_uget_borrowed(v_bs_3514_, v_i_3513_);
lean_inc(v_v_3517_);
v___x_3518_ = l_Lean_Json_getStr_x3f(v_v_3517_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v_bs_3514_);
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3528_; lean_object* v_bs_x27_3529_; size_t v___x_3530_; size_t v___x_3531_; lean_object* v___x_3532_; 
v_a_3527_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3518_);
v___x_3528_ = lean_unsigned_to_nat(0u);
v_bs_x27_3529_ = lean_array_uset(v_bs_3514_, v_i_3513_, v___x_3528_);
v___x_3530_ = ((size_t)1ULL);
v___x_3531_ = lean_usize_add(v_i_3513_, v___x_3530_);
v___x_3532_ = lean_array_uset(v_bs_x27_3529_, v_i_3513_, v_a_3527_);
v_i_3513_ = v___x_3531_;
v_bs_3514_ = v___x_3532_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3534_, lean_object* v_i_3535_, lean_object* v_bs_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3534_);
lean_dec(v_sz_3534_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3537_, v_i_boxed_3538_, v_bs_3536_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3540_){
_start:
{
if (lean_obj_tag(v_x_3540_) == 4)
{
lean_object* v_elems_3541_; size_t v_sz_3542_; size_t v___x_3543_; lean_object* v___x_3544_; 
v_elems_3541_ = lean_ctor_get(v_x_3540_, 0);
lean_inc_ref(v_elems_3541_);
lean_dec_ref(v_x_3540_);
v_sz_3542_ = lean_array_size(v_elems_3541_);
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3542_, v___x_3543_, v_elems_3541_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3545_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3546_ = lean_unsigned_to_nat(80u);
v___x_3547_ = l_Lean_Json_pretty(v_x_3540_, v___x_3546_);
v___x_3548_ = lean_string_append(v___x_3545_, v___x_3547_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3550_ = lean_string_append(v___x_3548_, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3552_, lean_object* v_k_3553_){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = l_Lean_Json_getObjValD(v_j_3552_, v_k_3553_);
v___x_3555_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3556_, lean_object* v_k_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3556_, v_k_3557_);
lean_dec_ref(v_k_3557_);
return v_res_3558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = 1;
v___x_3566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3570_ = lean_string_append(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = 1;
v___x_3574_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3575_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3577_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3578_ = lean_string_append(v___x_3577_, v___x_3576_);
return v___x_3578_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3580_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3581_ = lean_string_append(v___x_3580_, v___x_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3584_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3582_, v___x_3583_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3594_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3587_ = v___x_3584_;
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3594_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3589_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3590_ = lean_string_append(v___x_3589_, v_a_3585_);
lean_dec(v_a_3585_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v___x_3590_);
v___x_3592_ = v___x_3587_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
v_a_3595_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3584_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3584_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 0);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_a_3603_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3584_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3584_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3613_, size_t v_i_3614_, lean_object* v_bs_3615_){
_start:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_usize_dec_lt(v_i_3614_, v_sz_3613_);
if (v___x_3616_ == 0)
{
return v_bs_3615_;
}
else
{
lean_object* v_v_3617_; lean_object* v___x_3618_; lean_object* v_bs_x27_3619_; lean_object* v___x_3620_; size_t v___x_3621_; size_t v___x_3622_; lean_object* v___x_3623_; 
v_v_3617_ = lean_array_uget(v_bs_3615_, v_i_3614_);
v___x_3618_ = lean_unsigned_to_nat(0u);
v_bs_x27_3619_ = lean_array_uset(v_bs_3615_, v_i_3614_, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3620_, 0, v_v_3617_);
v___x_3621_ = ((size_t)1ULL);
v___x_3622_ = lean_usize_add(v_i_3614_, v___x_3621_);
v___x_3623_ = lean_array_uset(v_bs_x27_3619_, v_i_3614_, v___x_3620_);
v_i_3614_ = v___x_3622_;
v_bs_3615_ = v___x_3623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_bs_3627_){
_start:
{
size_t v_sz_boxed_3628_; size_t v_i_boxed_3629_; lean_object* v_res_3630_; 
v_sz_boxed_3628_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3629_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3628_, v_i_boxed_3629_, v_bs_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3631_){
_start:
{
size_t v_sz_3632_; size_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v_sz_3632_ = lean_array_size(v_a_3631_);
v___x_3633_ = ((size_t)0ULL);
v___x_3634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3632_, v___x_3633_, v_a_3631_);
v___x_3635_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3636_){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3637_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3638_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3636_);
v___x_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3637_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3639_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___x_3640_);
v___x_3643_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3644_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3642_, v___x_3643_);
v___x_3645_ = l_Lean_Json_mkObj(v___x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3648_, lean_object* v_k_3649_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = l_Lean_Json_getObjValD(v_j_3648_, v_k_3649_);
v___x_3651_ = l_Lean_Json_getStr_x3f(v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3652_, lean_object* v_k_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3652_, v_k_3653_);
lean_dec_ref(v_k_3653_);
return v_res_3654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = 1;
v___x_3662_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3666_ = lean_string_append(v___x_3665_, v___x_3664_);
return v___x_3666_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = 1;
v___x_3670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3674_ = lean_string_append(v___x_3673_, v___x_3672_);
return v___x_3674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3677_ = lean_string_append(v___x_3676_, v___x_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3678_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3680_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3678_, v___x_3679_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3690_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3690_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3690_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3685_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3686_ = lean_string_append(v___x_3685_, v_a_3681_);
lean_dec(v_a_3681_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3686_);
v___x_3688_ = v___x_3683_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
else
{
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
v_a_3691_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3680_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3680_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set_tag(v___x_3693_, 0);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3680_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3680_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3709_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3711_, 0, v_x_3709_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___x_3713_);
v___x_3716_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3717_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3715_, v___x_3716_);
v___x_3718_ = l_Lean_Json_mkObj(v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3721_){
_start:
{
if (lean_obj_tag(v_x_3721_) == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_unsigned_to_nat(0u);
return v___x_3722_;
}
else
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_unsigned_to_nat(1u);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3724_);
lean_dec_ref(v_x_3724_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3726_, lean_object* v_k_3727_){
_start:
{
if (lean_obj_tag(v_t_3726_) == 0)
{
lean_object* v_namespace_3728_; lean_object* v_exceptions_3729_; lean_object* v___x_3730_; 
v_namespace_3728_ = lean_ctor_get(v_t_3726_, 0);
lean_inc(v_namespace_3728_);
v_exceptions_3729_ = lean_ctor_get(v_t_3726_, 1);
lean_inc_ref(v_exceptions_3729_);
lean_dec_ref(v_t_3726_);
v___x_3730_ = lean_apply_2(v_k_3727_, v_namespace_3728_, v_exceptions_3729_);
return v___x_3730_;
}
else
{
lean_object* v_from_3731_; lean_object* v_to_3732_; lean_object* v___x_3733_; 
v_from_3731_ = lean_ctor_get(v_t_3726_, 0);
lean_inc(v_from_3731_);
v_to_3732_ = lean_ctor_get(v_t_3726_, 1);
lean_inc(v_to_3732_);
lean_dec_ref(v_t_3726_);
v___x_3733_ = lean_apply_2(v_k_3727_, v_from_3731_, v_to_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3734_, lean_object* v_ctorIdx_3735_, lean_object* v_t_3736_, lean_object* v_h_3737_, lean_object* v_k_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3736_, v_k_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3740_, lean_object* v_ctorIdx_3741_, lean_object* v_t_3742_, lean_object* v_h_3743_, lean_object* v_k_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3740_, v_ctorIdx_3741_, v_t_3742_, v_h_3743_, v_k_3744_);
lean_dec(v_ctorIdx_3741_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3746_, lean_object* v_allExcept_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3746_, v_allExcept_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3749_, lean_object* v_t_3750_, lean_object* v_h_3751_, lean_object* v_allExcept_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3750_, v_allExcept_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3754_, lean_object* v_renamed_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3754_, v_renamed_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3757_, lean_object* v_t_3758_, lean_object* v_h_3759_, lean_object* v_renamed_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3758_, v_renamed_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3762_, size_t v_i_3763_, lean_object* v_bs_3764_){
_start:
{
uint8_t v___x_3765_; 
v___x_3765_ = lean_usize_dec_lt(v_i_3763_, v_sz_3762_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_bs_3764_);
return v___x_3766_;
}
else
{
lean_object* v_v_3767_; lean_object* v___x_3768_; 
v_v_3767_ = lean_array_uget_borrowed(v_bs_3764_, v_i_3763_);
lean_inc(v_v_3767_);
v___x_3768_ = l_Lean_Name_fromJson_x3f(v_v_3767_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v_bs_3764_);
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3778_; lean_object* v_bs_x27_3779_; size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v_a_3777_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3768_);
v___x_3778_ = lean_unsigned_to_nat(0u);
v_bs_x27_3779_ = lean_array_uset(v_bs_3764_, v_i_3763_, v___x_3778_);
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3763_, v___x_3780_);
v___x_3782_ = lean_array_uset(v_bs_x27_3779_, v_i_3763_, v_a_3777_);
v_i_3763_ = v___x_3781_;
v_bs_3764_ = v___x_3782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3784_, lean_object* v_i_3785_, lean_object* v_bs_3786_){
_start:
{
size_t v_sz_boxed_3787_; size_t v_i_boxed_3788_; lean_object* v_res_3789_; 
v_sz_boxed_3787_ = lean_unbox_usize(v_sz_3784_);
lean_dec(v_sz_3784_);
v_i_boxed_3788_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_res_3789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3787_, v_i_boxed_3788_, v_bs_3786_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 4)
{
lean_object* v_elems_3791_; size_t v_sz_3792_; size_t v___x_3793_; lean_object* v___x_3794_; 
v_elems_3791_ = lean_ctor_get(v_x_3790_, 0);
lean_inc_ref(v_elems_3791_);
lean_dec_ref(v_x_3790_);
v_sz_3792_ = lean_array_size(v_elems_3791_);
v___x_3793_ = ((size_t)0ULL);
v___x_3794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3792_, v___x_3793_, v_elems_3791_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3795_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3796_ = lean_unsigned_to_nat(80u);
v___x_3797_ = l_Lean_Json_pretty(v_x_3790_, v___x_3796_);
v___x_3798_ = lean_string_append(v___x_3795_, v___x_3797_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3800_ = lean_string_append(v___x_3798_, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
return v___x_3801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3836_){
_start:
{
lean_object* v___x_3837_; 
lean_inc(v_json_3836_);
v___x_3837_ = l_Lean_Json_getTag_x3f(v_json_3836_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v___x_3838_; 
lean_dec(v_json_3836_);
v___x_3838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3838_;
}
else
{
lean_object* v_val_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_val_3839_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_val_3839_);
lean_dec_ref(v___x_3837_);
v___x_3840_ = lean_box(0);
v___x_3841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3842_ = lean_string_dec_eq(v_val_3839_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3844_ = lean_string_dec_eq(v_val_3839_, v___x_3843_);
lean_dec(v_val_3839_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; 
lean_dec(v_json_3836_);
v___x_3845_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3845_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_unsigned_to_nat(2u);
v___x_3847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3848_ = l_Lean_Json_parseCtorFields(v_json_3836_, v___x_3843_, v___x_3846_, v___x_3847_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v_a_3857_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3848_);
v___x_3858_ = lean_unsigned_to_nat(0u);
v___x_3859_ = lean_array_get_borrowed(v___x_3840_, v_a_3857_, v___x_3858_);
lean_inc(v___x_3859_);
v___x_3860_ = l_Lean_Name_fromJson_x3f(v___x_3859_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_a_3857_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_a_3869_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3860_);
v___x_3870_ = lean_unsigned_to_nat(1u);
v___x_3871_ = lean_array_get(v___x_3840_, v_a_3857_, v___x_3870_);
lean_dec(v_a_3857_);
v___x_3872_ = l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_a_3869_);
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
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3889_; 
v_a_3881_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3883_ = v___x_3872_;
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3872_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3889_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_a_3869_);
lean_ctor_set(v___x_3885_, 1, v_a_3881_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3885_);
v___x_3887_ = v___x_3883_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
lean_dec(v_val_3839_);
v___x_3890_ = lean_unsigned_to_nat(2u);
v___x_3891_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3892_ = l_Lean_Json_parseCtorFields(v_json_3836_, v___x_3841_, v___x_3890_, v___x_3891_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_a_3901_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3901_);
lean_dec_ref(v___x_3892_);
v___x_3902_ = lean_unsigned_to_nat(0u);
v___x_3903_ = lean_array_get_borrowed(v___x_3840_, v_a_3901_, v___x_3902_);
lean_inc(v___x_3903_);
v___x_3904_ = l_Lean_Name_fromJson_x3f(v___x_3903_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_a_3901_);
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3913_);
lean_dec_ref(v___x_3904_);
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_array_get(v___x_3840_, v_a_3901_, v___x_3914_);
lean_dec(v_a_3901_);
v___x_3916_ = l_Lean_Name_fromJson_x3f(v___x_3915_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_a_3913_);
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3933_; 
v_a_3925_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3927_ = v___x_3916_;
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3916_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_a_3913_);
lean_ctor_set(v___x_3929_, 1, v_a_3925_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3936_, size_t v_i_3937_, lean_object* v_bs_3938_){
_start:
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_usize_dec_lt(v_i_3937_, v_sz_3936_);
if (v___x_3939_ == 0)
{
return v_bs_3938_;
}
else
{
lean_object* v_v_3940_; lean_object* v___x_3941_; lean_object* v_bs_x27_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; lean_object* v___x_3947_; 
v_v_3940_ = lean_array_uget(v_bs_3938_, v_i_3937_);
v___x_3941_ = lean_unsigned_to_nat(0u);
v_bs_x27_3942_ = lean_array_uset(v_bs_3938_, v_i_3937_, v___x_3941_);
v___x_3943_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3940_, v___x_3939_);
v___x_3944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_add(v_i_3937_, v___x_3945_);
v___x_3947_ = lean_array_uset(v_bs_x27_3942_, v_i_3937_, v___x_3944_);
v_i_3937_ = v___x_3946_;
v_bs_3938_ = v___x_3947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3949_, lean_object* v_i_3950_, lean_object* v_bs_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3949_);
lean_dec(v_sz_3949_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3950_);
lean_dec(v_i_3950_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3952_, v_i_boxed_3953_, v_bs_3951_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3955_){
_start:
{
size_t v_sz_3956_; size_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_sz_3956_ = lean_array_size(v_a_3955_);
v___x_3957_ = ((size_t)0ULL);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3956_, v___x_3957_, v_a_3955_);
v___x_3959_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3960_){
_start:
{
if (lean_obj_tag(v_x_3960_) == 0)
{
lean_object* v_namespace_3961_; lean_object* v_exceptions_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3984_; 
v_namespace_3961_ = lean_ctor_get(v_x_3960_, 0);
v_exceptions_3962_ = lean_ctor_get(v_x_3960_, 1);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_x_3960_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3964_ = v_x_3960_;
v_isShared_3965_ = v_isSharedCheck_3984_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_exceptions_3962_);
lean_inc(v_namespace_3961_);
lean_dec(v_x_3960_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3984_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3968_ = 1;
v___x_3969_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3961_, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 1, v___x_3970_);
lean_ctor_set(v___x_3964_, 0, v___x_3967_);
v___x_3972_ = v___x_3964_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3974_ = l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3962_);
v___x_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3972_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = l_Lean_Json_mkObj(v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3966_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
lean_ctor_set(v___x_3981_, 1, v___x_3976_);
v___x_3982_ = l_Lean_Json_mkObj(v___x_3981_);
return v___x_3982_;
}
}
}
else
{
lean_object* v_from_3985_; lean_object* v_to_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4009_; 
v_from_3985_ = lean_ctor_get(v_x_3960_, 0);
v_to_3986_ = lean_ctor_get(v_x_3960_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_x_3960_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3988_ = v_x_3960_;
v_isShared_3989_ = v_isSharedCheck_4009_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_to_3986_);
lean_inc(v_from_3985_);
lean_dec(v_x_3960_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4009_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3992_ = 1;
v___x_3993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3985_, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set_tag(v___x_3988_, 0);
lean_ctor_set(v___x_3988_, 1, v___x_3994_);
lean_ctor_set(v___x_3988_, 0, v___x_3991_);
v___x_3996_ = v___x_3988_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_4008_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_3997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3998_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3986_, v___x_3992_);
v___x_3999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3997_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = lean_box(0);
v___x_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4000_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3996_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l_Lean_Json_mkObj(v___x_4003_);
v___x_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_3990_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v___x_4001_);
v___x_4007_ = l_Lean_Json_mkObj(v___x_4006_);
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4012_, size_t v_i_4013_, lean_object* v_bs_4014_){
_start:
{
uint8_t v___x_4015_; 
v___x_4015_ = lean_usize_dec_lt(v_i_4013_, v_sz_4012_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_bs_4014_);
return v___x_4016_;
}
else
{
lean_object* v_v_4017_; lean_object* v___x_4018_; 
v_v_4017_ = lean_array_uget_borrowed(v_bs_4014_, v_i_4013_);
lean_inc(v_v_4017_);
v___x_4018_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_4017_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec_ref(v_bs_4014_);
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v_bs_x27_4029_; size_t v___x_4030_; size_t v___x_4031_; lean_object* v___x_4032_; 
v_a_4027_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4018_);
v___x_4028_ = lean_unsigned_to_nat(0u);
v_bs_x27_4029_ = lean_array_uset(v_bs_4014_, v_i_4013_, v___x_4028_);
v___x_4030_ = ((size_t)1ULL);
v___x_4031_ = lean_usize_add(v_i_4013_, v___x_4030_);
v___x_4032_ = lean_array_uset(v_bs_x27_4029_, v_i_4013_, v_a_4027_);
v_i_4013_ = v___x_4031_;
v_bs_4014_ = v___x_4032_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4034_, lean_object* v_i_4035_, lean_object* v_bs_4036_){
_start:
{
size_t v_sz_boxed_4037_; size_t v_i_boxed_4038_; lean_object* v_res_4039_; 
v_sz_boxed_4037_ = lean_unbox_usize(v_sz_4034_);
lean_dec(v_sz_4034_);
v_i_boxed_4038_ = lean_unbox_usize(v_i_4035_);
lean_dec(v_i_4035_);
v_res_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4037_, v_i_boxed_4038_, v_bs_4036_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4040_) == 4)
{
lean_object* v_elems_4041_; size_t v_sz_4042_; size_t v___x_4043_; lean_object* v___x_4044_; 
v_elems_4041_ = lean_ctor_get(v_x_4040_, 0);
lean_inc_ref(v_elems_4041_);
lean_dec_ref(v_x_4040_);
v_sz_4042_ = lean_array_size(v_elems_4041_);
v___x_4043_ = ((size_t)0ULL);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4042_, v___x_4043_, v_elems_4041_);
return v___x_4044_;
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4045_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4046_ = lean_unsigned_to_nat(80u);
v___x_4047_ = l_Lean_Json_pretty(v_x_4040_, v___x_4046_);
v___x_4048_ = lean_string_append(v___x_4045_, v___x_4047_);
lean_dec_ref(v___x_4047_);
v___x_4049_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4050_ = lean_string_append(v___x_4048_, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4052_, lean_object* v_k_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = l_Lean_Json_getObjValD(v_j_4052_, v_k_4053_);
v___x_4055_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4056_, lean_object* v_k_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4056_, v_k_4057_);
lean_dec_ref(v_k_4057_);
return v_res_4058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = 1;
v___x_4066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4066_, v___x_4065_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4070_ = lean_string_append(v___x_4069_, v___x_4068_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = 1;
v___x_4074_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4075_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4074_, v___x_4073_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4077_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4078_ = lean_string_append(v___x_4077_, v___x_4076_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4080_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4081_ = lean_string_append(v___x_4080_, v___x_4079_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = 1;
v___x_4086_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4086_, v___x_4085_);
return v___x_4087_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4089_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4090_ = lean_string_append(v___x_4089_, v___x_4088_);
return v___x_4090_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4092_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4093_ = lean_string_append(v___x_4092_, v___x_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4094_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4094_);
v___x_4096_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4094_, v___x_4095_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_json_4094_);
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4106_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4102_ = lean_string_append(v___x_4101_, v_a_4097_);
lean_dec(v_a_4097_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4102_);
v___x_4104_ = v___x_4099_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
else
{
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_json_4094_);
v_a_4107_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4096_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4096_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 0);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_a_4115_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4115_);
lean_dec_ref(v___x_4096_);
v___x_4116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4117_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4094_, v___x_4116_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_a_4115_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4127_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4123_ = lean_string_append(v___x_4122_, v_a_4118_);
lean_dec(v_a_4118_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4123_);
v___x_4125_ = v___x_4120_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_a_4115_);
v_a_4128_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4117_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4117_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 0);
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4144_; 
v_a_4136_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4138_ = v___x_4117_;
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4117_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v_a_4115_);
lean_ctor_set(v___x_4140_, 1, v_a_4136_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4140_);
v___x_4142_ = v___x_4138_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4147_, size_t v_i_4148_, lean_object* v_bs_4149_){
_start:
{
uint8_t v___x_4150_; 
v___x_4150_ = lean_usize_dec_lt(v_i_4148_, v_sz_4147_);
if (v___x_4150_ == 0)
{
return v_bs_4149_;
}
else
{
lean_object* v_v_4151_; lean_object* v___x_4152_; lean_object* v_bs_x27_4153_; lean_object* v___x_4154_; size_t v___x_4155_; size_t v___x_4156_; lean_object* v___x_4157_; 
v_v_4151_ = lean_array_uget(v_bs_4149_, v_i_4148_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v_bs_x27_4153_ = lean_array_uset(v_bs_4149_, v_i_4148_, v___x_4152_);
v___x_4154_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4151_);
v___x_4155_ = ((size_t)1ULL);
v___x_4156_ = lean_usize_add(v_i_4148_, v___x_4155_);
v___x_4157_ = lean_array_uset(v_bs_x27_4153_, v_i_4148_, v___x_4154_);
v_i_4148_ = v___x_4156_;
v_bs_4149_ = v___x_4157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4159_, lean_object* v_i_4160_, lean_object* v_bs_4161_){
_start:
{
size_t v_sz_boxed_4162_; size_t v_i_boxed_4163_; lean_object* v_res_4164_; 
v_sz_boxed_4162_ = lean_unbox_usize(v_sz_4159_);
lean_dec(v_sz_4159_);
v_i_boxed_4163_ = lean_unbox_usize(v_i_4160_);
lean_dec(v_i_4160_);
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4162_, v_i_boxed_4163_, v_bs_4161_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4165_){
_start:
{
size_t v_sz_4166_; size_t v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_sz_4166_ = lean_array_size(v_a_4165_);
v___x_4167_ = ((size_t)0ULL);
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4166_, v___x_4167_, v_a_4165_);
v___x_4169_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4170_){
_start:
{
lean_object* v_identifier_4171_; lean_object* v_openNamespaces_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4192_; 
v_identifier_4171_ = lean_ctor_get(v_x_4170_, 0);
v_openNamespaces_4172_ = lean_ctor_get(v_x_4170_, 1);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_x_4170_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4174_ = v_x_4170_;
v_isShared_4175_ = v_isSharedCheck_4192_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_openNamespaces_4172_);
lean_inc(v_identifier_4171_);
lean_dec(v_x_4170_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4192_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4177_, 0, v_identifier_4171_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v___x_4177_);
lean_ctor_set(v___x_4174_, 0, v___x_4176_);
v___x_4179_ = v___x_4174_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4180_ = lean_box(0);
v___x_4181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4183_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4172_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4182_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___x_4180_);
v___x_4186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4180_);
v___x_4187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4181_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4189_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4187_, v___x_4188_);
v___x_4190_ = l_Lean_Json_mkObj(v___x_4189_);
return v___x_4190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4198_, lean_object* v_k_4199_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_Json_getObjValD(v_j_4198_, v_k_4199_);
switch(lean_obj_tag(v___x_4200_))
{
case 3:
{
lean_object* v_s_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4209_; 
v_s_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_s_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set_tag(v___x_4203_, 0);
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_s_4201_);
v___x_4206_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
case 2:
{
lean_object* v_n_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4218_; 
v_n_4210_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4212_ = v___x_4200_;
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_n_4210_);
lean_dec(v___x_4200_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4218_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
lean_ctor_set_tag(v___x_4212_, 1);
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_n_4210_);
v___x_4215_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
}
default: 
{
lean_object* v___x_4219_; 
lean_dec(v___x_4200_);
v___x_4219_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4220_, lean_object* v_k_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4220_, v_k_4221_);
lean_dec_ref(v_k_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_bs_4225_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4227_, 0, v_bs_4225_);
return v___x_4227_;
}
else
{
lean_object* v_v_4228_; lean_object* v___x_4229_; 
v_v_4228_ = lean_array_uget_borrowed(v_bs_4225_, v_i_4224_);
lean_inc(v_v_4228_);
v___x_4229_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4228_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v_bs_4225_);
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v_bs_x27_4240_; size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
v_a_4238_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4238_);
lean_dec_ref(v___x_4229_);
v___x_4239_ = lean_unsigned_to_nat(0u);
v_bs_x27_4240_ = lean_array_uset(v_bs_4225_, v_i_4224_, v___x_4239_);
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4224_, v___x_4241_);
v___x_4243_ = lean_array_uset(v_bs_x27_4240_, v_i_4224_, v_a_4238_);
v_i_4224_ = v___x_4242_;
v_bs_4225_ = v___x_4243_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_bs_4247_){
_start:
{
size_t v_sz_boxed_4248_; size_t v_i_boxed_4249_; lean_object* v_res_4250_; 
v_sz_boxed_4248_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4249_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4248_, v_i_boxed_4249_, v_bs_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4251_){
_start:
{
if (lean_obj_tag(v_x_4251_) == 4)
{
lean_object* v_elems_4252_; size_t v_sz_4253_; size_t v___x_4254_; lean_object* v___x_4255_; 
v_elems_4252_ = lean_ctor_get(v_x_4251_, 0);
lean_inc_ref(v_elems_4252_);
lean_dec_ref(v_x_4251_);
v_sz_4253_ = lean_array_size(v_elems_4252_);
v___x_4254_ = ((size_t)0ULL);
v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4253_, v___x_4254_, v_elems_4252_);
return v___x_4255_;
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4256_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4257_ = lean_unsigned_to_nat(80u);
v___x_4258_ = l_Lean_Json_pretty(v_x_4251_, v___x_4257_);
v___x_4259_ = lean_string_append(v___x_4256_, v___x_4258_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4261_ = lean_string_append(v___x_4259_, v___x_4260_);
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
return v___x_4262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4263_, lean_object* v_k_4264_){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = l_Lean_Json_getObjValD(v_j_4263_, v_k_4264_);
v___x_4266_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4267_, lean_object* v_k_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4267_, v_k_4268_);
lean_dec_ref(v_k_4268_);
return v_res_4269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = 1;
v___x_4277_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4278_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4277_, v___x_4276_);
return v___x_4278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4281_ = lean_string_append(v___x_4280_, v___x_4279_);
return v___x_4281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4284_ = 1;
v___x_4285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4286_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4285_, v___x_4284_);
return v___x_4286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4288_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4289_ = lean_string_append(v___x_4288_, v___x_4287_);
return v___x_4289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4290_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4291_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4292_ = lean_string_append(v___x_4291_, v___x_4290_);
return v___x_4292_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = 1;
v___x_4297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4298_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4297_, v___x_4296_);
return v___x_4298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4300_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4301_ = lean_string_append(v___x_4300_, v___x_4299_);
return v___x_4301_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4303_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4304_ = lean_string_append(v___x_4303_, v___x_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4305_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4305_);
v___x_4307_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4305_, v___x_4306_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_json_4305_);
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4317_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4317_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4312_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4313_ = lean_string_append(v___x_4312_, v_a_4308_);
lean_dec(v_a_4308_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v___x_4313_);
v___x_4315_ = v___x_4310_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
else
{
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec(v_json_4305_);
v_a_4318_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4307_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4307_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
lean_ctor_set_tag(v___x_4320_, 0);
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v_a_4326_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4326_);
lean_dec_ref(v___x_4307_);
v___x_4327_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4328_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4305_, v___x_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_a_4326_);
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4338_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4338_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4333_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4334_ = lean_string_append(v___x_4333_, v_a_4329_);
lean_dec(v_a_4329_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v___x_4334_);
v___x_4336_ = v___x_4331_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_a_4326_);
v_a_4339_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4328_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4328_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 0);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4355_; 
v_a_4347_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4349_ = v___x_4328_;
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4328_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_a_4326_);
lean_ctor_set(v___x_4351_, 1, v_a_4347_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4351_);
v___x_4353_ = v___x_4349_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4358_, size_t v_i_4359_, lean_object* v_bs_4360_){
_start:
{
uint8_t v___x_4361_; 
v___x_4361_ = lean_usize_dec_lt(v_i_4359_, v_sz_4358_);
if (v___x_4361_ == 0)
{
return v_bs_4360_;
}
else
{
lean_object* v_v_4362_; lean_object* v___x_4363_; lean_object* v_bs_x27_4364_; lean_object* v___x_4365_; size_t v___x_4366_; size_t v___x_4367_; lean_object* v___x_4368_; 
v_v_4362_ = lean_array_uget(v_bs_4360_, v_i_4359_);
v___x_4363_ = lean_unsigned_to_nat(0u);
v_bs_x27_4364_ = lean_array_uset(v_bs_4360_, v_i_4359_, v___x_4363_);
v___x_4365_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4362_);
v___x_4366_ = ((size_t)1ULL);
v___x_4367_ = lean_usize_add(v_i_4359_, v___x_4366_);
v___x_4368_ = lean_array_uset(v_bs_x27_4364_, v_i_4359_, v___x_4365_);
v_i_4359_ = v___x_4367_;
v_bs_4360_ = v___x_4368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_bs_4372_){
_start:
{
size_t v_sz_boxed_4373_; size_t v_i_boxed_4374_; lean_object* v_res_4375_; 
v_sz_boxed_4373_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4374_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4373_, v_i_boxed_4374_, v_bs_4372_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4376_){
_start:
{
size_t v_sz_4377_; size_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_sz_4377_ = lean_array_size(v_a_4376_);
v___x_4378_ = ((size_t)0ULL);
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4377_, v___x_4378_, v_a_4376_);
v___x_4380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4381_){
_start:
{
lean_object* v_sourceRequestID_4382_; lean_object* v_queries_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4421_; 
v_sourceRequestID_4382_ = lean_ctor_get(v_x_4381_, 0);
v_queries_4383_ = lean_ctor_get(v_x_4381_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_x_4381_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4385_ = v_x_4381_;
v_isShared_4386_ = v_isSharedCheck_4421_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_queries_4383_);
lean_inc(v_sourceRequestID_4382_);
lean_dec(v_x_4381_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4421_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v___y_4389_; 
v___x_4387_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4382_))
{
case 0:
{
lean_object* v_s_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
v_s_4404_ = lean_ctor_get(v_sourceRequestID_4382_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_sourceRequestID_4382_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v_sourceRequestID_4382_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_s_4404_);
lean_dec(v_sourceRequestID_4382_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set_tag(v___x_4406_, 3);
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_s_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
v___y_4389_ = v___x_4409_;
goto v___jp_4388_;
}
}
}
case 1:
{
lean_object* v_n_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
v_n_4412_ = lean_ctor_get(v_sourceRequestID_4382_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_sourceRequestID_4382_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v_sourceRequestID_4382_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_n_4412_);
lean_dec(v_sourceRequestID_4382_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
lean_ctor_set_tag(v___x_4414_, 2);
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_n_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
v___y_4389_ = v___x_4417_;
goto v___jp_4388_;
}
}
}
default: 
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_box(0);
v___y_4389_ = v___x_4420_;
goto v___jp_4388_;
}
}
v___jp_4388_:
{
lean_object* v___x_4391_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 1, v___y_4389_);
lean_ctor_set(v___x_4385_, 0, v___x_4387_);
v___x_4391_ = v___x_4385_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v___y_4389_);
v___x_4391_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4392_ = lean_box(0);
v___x_4393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4395_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4383_);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4394_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___x_4392_);
v___x_4398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
lean_ctor_set(v___x_4398_, 1, v___x_4392_);
v___x_4399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4393_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4401_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4399_, v___x_4400_);
v___x_4402_ = l_Lean_Json_mkObj(v___x_4401_);
return v___x_4402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4424_, lean_object* v_k_4425_){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = l_Lean_Json_getObjValD(v_j_4424_, v_k_4425_);
v___x_4427_ = l_Lean_Name_fromJson_x3f(v___x_4426_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4428_, lean_object* v_k_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4428_, v_k_4429_);
lean_dec_ref(v_k_4429_);
return v_res_4430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = 1;
v___x_4438_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4439_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4438_, v___x_4437_);
return v___x_4439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4441_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4442_ = lean_string_append(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4445_ = 1;
v___x_4446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4447_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4446_, v___x_4445_);
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4450_ = lean_string_append(v___x_4449_, v___x_4448_);
return v___x_4450_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4451_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4452_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4453_ = lean_string_append(v___x_4452_, v___x_4451_);
return v___x_4453_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = 1;
v___x_4458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4458_, v___x_4457_);
return v___x_4459_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4460_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4461_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4462_ = lean_string_append(v___x_4461_, v___x_4460_);
return v___x_4462_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4464_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4465_ = lean_string_append(v___x_4464_, v___x_4463_);
return v___x_4465_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = 1;
v___x_4470_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4470_, v___x_4469_);
return v___x_4471_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4473_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4474_ = lean_string_append(v___x_4473_, v___x_4472_);
return v___x_4474_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4476_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4477_ = lean_string_append(v___x_4476_, v___x_4475_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4478_){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4478_);
v___x_4480_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4478_, v___x_4479_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v_json_4478_);
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4483_ = v___x_4480_;
v_isShared_4484_ = v_isSharedCheck_4490_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4490_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4485_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4486_ = lean_string_append(v___x_4485_, v_a_4481_);
lean_dec(v_a_4481_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4486_);
v___x_4488_ = v___x_4483_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
else
{
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_json_4478_);
v_a_4491_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4480_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4480_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set_tag(v___x_4493_, 0);
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4499_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4480_);
v___x_4500_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4478_);
v___x_4501_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4478_, v___x_4500_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_a_4499_);
lean_dec(v_json_4478_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4511_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4511_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; 
v___x_4506_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4507_ = lean_string_append(v___x_4506_, v_a_4502_);
lean_dec(v_a_4502_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4507_);
v___x_4509_ = v___x_4504_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
else
{
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec(v_a_4499_);
lean_dec(v_json_4478_);
v_a_4512_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4501_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4501_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set_tag(v___x_4514_, 0);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4520_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4520_);
lean_dec_ref(v___x_4501_);
v___x_4521_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4522_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4478_, v___x_4521_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4532_; 
lean_dec(v_a_4520_);
lean_dec(v_a_4499_);
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4525_ = v___x_4522_;
v_isShared_4526_ = v_isSharedCheck_4532_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4532_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4528_ = lean_string_append(v___x_4527_, v_a_4523_);
lean_dec(v_a_4523_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4528_);
v___x_4530_ = v___x_4525_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
else
{
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec(v_a_4520_);
lean_dec(v_a_4499_);
v_a_4533_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4522_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4522_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
lean_ctor_set_tag(v___x_4535_, 0);
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
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
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4550_; 
v_a_4541_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4543_ = v___x_4522_;
v_isShared_4544_ = v_isSharedCheck_4550_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4522_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4550_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; uint8_t v___x_4546_; lean_object* v___x_4548_; 
v___x_4545_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4545_, 0, v_a_4499_);
lean_ctor_set(v___x_4545_, 1, v_a_4520_);
v___x_4546_ = lean_unbox(v_a_4541_);
lean_dec(v_a_4541_);
lean_ctor_set_uint8(v___x_4545_, sizeof(void*)*2, v___x_4546_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4545_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4545_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4553_){
_start:
{
lean_object* v_module_4554_; lean_object* v_decl_4555_; uint8_t v_isExactMatch_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v_module_4554_ = lean_ctor_get(v_x_4553_, 0);
lean_inc(v_module_4554_);
v_decl_4555_ = lean_ctor_get(v_x_4553_, 1);
lean_inc(v_decl_4555_);
v_isExactMatch_4556_ = lean_ctor_get_uint8(v_x_4553_, sizeof(void*)*2);
lean_dec_ref(v_x_4553_);
v___x_4557_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4558_ = 1;
v___x_4559_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4554_, v___x_4558_);
v___x_4560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
v___x_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4557_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
v___x_4562_ = lean_box(0);
v___x_4563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4561_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4555_, v___x_4558_);
v___x_4566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
v___x_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4564_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
lean_ctor_set(v___x_4568_, 1, v___x_4562_);
v___x_4569_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4570_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4570_, 0, v_isExactMatch_4556_);
v___x_4571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
lean_ctor_set(v___x_4572_, 1, v___x_4562_);
v___x_4573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
lean_ctor_set(v___x_4573_, 1, v___x_4562_);
v___x_4574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4568_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
v___x_4575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4563_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4577_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4575_, v___x_4576_);
v___x_4578_ = l_Lean_Json_mkObj(v___x_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4581_, size_t v_i_4582_, lean_object* v_bs_4583_){
_start:
{
uint8_t v___x_4584_; 
v___x_4584_ = lean_usize_dec_lt(v_i_4582_, v_sz_4581_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4585_, 0, v_bs_4583_);
return v___x_4585_;
}
else
{
lean_object* v_v_4586_; lean_object* v___x_4587_; 
v_v_4586_ = lean_array_uget_borrowed(v_bs_4583_, v_i_4582_);
lean_inc(v_v_4586_);
v___x_4587_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4586_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec_ref(v_bs_4583_);
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4587_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4587_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4597_; lean_object* v_bs_x27_4598_; size_t v___x_4599_; size_t v___x_4600_; lean_object* v___x_4601_; 
v_a_4596_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4596_);
lean_dec_ref(v___x_4587_);
v___x_4597_ = lean_unsigned_to_nat(0u);
v_bs_x27_4598_ = lean_array_uset(v_bs_4583_, v_i_4582_, v___x_4597_);
v___x_4599_ = ((size_t)1ULL);
v___x_4600_ = lean_usize_add(v_i_4582_, v___x_4599_);
v___x_4601_ = lean_array_uset(v_bs_x27_4598_, v_i_4582_, v_a_4596_);
v_i_4582_ = v___x_4600_;
v_bs_4583_ = v___x_4601_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4603_, lean_object* v_i_4604_, lean_object* v_bs_4605_){
_start:
{
size_t v_sz_boxed_4606_; size_t v_i_boxed_4607_; lean_object* v_res_4608_; 
v_sz_boxed_4606_ = lean_unbox_usize(v_sz_4603_);
lean_dec(v_sz_4603_);
v_i_boxed_4607_ = lean_unbox_usize(v_i_4604_);
lean_dec(v_i_4604_);
v_res_4608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4606_, v_i_boxed_4607_, v_bs_4605_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4609_){
_start:
{
if (lean_obj_tag(v_x_4609_) == 4)
{
lean_object* v_elems_4610_; size_t v_sz_4611_; size_t v___x_4612_; lean_object* v___x_4613_; 
v_elems_4610_ = lean_ctor_get(v_x_4609_, 0);
lean_inc_ref(v_elems_4610_);
lean_dec_ref(v_x_4609_);
v_sz_4611_ = lean_array_size(v_elems_4610_);
v___x_4612_ = ((size_t)0ULL);
v___x_4613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4611_, v___x_4612_, v_elems_4610_);
return v___x_4613_;
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4614_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4615_ = lean_unsigned_to_nat(80u);
v___x_4616_ = l_Lean_Json_pretty(v_x_4609_, v___x_4615_);
v___x_4617_ = lean_string_append(v___x_4614_, v___x_4616_);
lean_dec_ref(v___x_4616_);
v___x_4618_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4619_ = lean_string_append(v___x_4617_, v___x_4618_);
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4621_, size_t v_i_4622_, lean_object* v_bs_4623_){
_start:
{
uint8_t v___x_4624_; 
v___x_4624_ = lean_usize_dec_lt(v_i_4622_, v_sz_4621_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_bs_4623_);
return v___x_4625_;
}
else
{
lean_object* v_v_4626_; lean_object* v___x_4627_; 
v_v_4626_ = lean_array_uget_borrowed(v_bs_4623_, v_i_4622_);
lean_inc(v_v_4626_);
v___x_4627_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4626_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v_bs_4623_);
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4627_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4627_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4637_; lean_object* v_bs_x27_4638_; size_t v___x_4639_; size_t v___x_4640_; lean_object* v___x_4641_; 
v_a_4636_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4636_);
lean_dec_ref(v___x_4627_);
v___x_4637_ = lean_unsigned_to_nat(0u);
v_bs_x27_4638_ = lean_array_uset(v_bs_4623_, v_i_4622_, v___x_4637_);
v___x_4639_ = ((size_t)1ULL);
v___x_4640_ = lean_usize_add(v_i_4622_, v___x_4639_);
v___x_4641_ = lean_array_uset(v_bs_x27_4638_, v_i_4622_, v_a_4636_);
v_i_4622_ = v___x_4640_;
v_bs_4623_ = v___x_4641_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4643_, lean_object* v_i_4644_, lean_object* v_bs_4645_){
_start:
{
size_t v_sz_boxed_4646_; size_t v_i_boxed_4647_; lean_object* v_res_4648_; 
v_sz_boxed_4646_ = lean_unbox_usize(v_sz_4643_);
lean_dec(v_sz_4643_);
v_i_boxed_4647_ = lean_unbox_usize(v_i_4644_);
lean_dec(v_i_4644_);
v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4646_, v_i_boxed_4647_, v_bs_4645_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4649_){
_start:
{
if (lean_obj_tag(v_x_4649_) == 4)
{
lean_object* v_elems_4650_; size_t v_sz_4651_; size_t v___x_4652_; lean_object* v___x_4653_; 
v_elems_4650_ = lean_ctor_get(v_x_4649_, 0);
lean_inc_ref(v_elems_4650_);
lean_dec_ref(v_x_4649_);
v_sz_4651_ = lean_array_size(v_elems_4650_);
v___x_4652_ = ((size_t)0ULL);
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4651_, v___x_4652_, v_elems_4650_);
return v___x_4653_;
}
else
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4654_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4655_ = lean_unsigned_to_nat(80u);
v___x_4656_ = l_Lean_Json_pretty(v_x_4649_, v___x_4655_);
v___x_4657_ = lean_string_append(v___x_4654_, v___x_4656_);
lean_dec_ref(v___x_4656_);
v___x_4658_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4659_ = lean_string_append(v___x_4657_, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4661_, lean_object* v_k_4662_){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = l_Lean_Json_getObjValD(v_j_4661_, v_k_4662_);
v___x_4664_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4665_, lean_object* v_k_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4665_, v_k_4666_);
lean_dec_ref(v_k_4666_);
return v_res_4667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = 1;
v___x_4675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4679_ = lean_string_append(v___x_4678_, v___x_4677_);
return v___x_4679_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = 1;
v___x_4683_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4683_, v___x_4682_);
return v___x_4684_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4686_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4687_ = lean_string_append(v___x_4686_, v___x_4685_);
return v___x_4687_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4689_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4690_ = lean_string_append(v___x_4689_, v___x_4688_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4691_){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4693_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4691_, v___x_4692_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4703_; 
v_a_4694_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4696_ = v___x_4693_;
v_isShared_4697_ = v_isSharedCheck_4703_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4693_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4703_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4701_; 
v___x_4698_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4699_ = lean_string_append(v___x_4698_, v_a_4694_);
lean_dec(v_a_4694_);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4699_);
v___x_4701_ = v___x_4696_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4699_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
else
{
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
v_a_4704_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4693_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4693_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 0);
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4693_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4693_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4722_, size_t v_i_4723_, lean_object* v_bs_4724_){
_start:
{
uint8_t v___x_4725_; 
v___x_4725_ = lean_usize_dec_lt(v_i_4723_, v_sz_4722_);
if (v___x_4725_ == 0)
{
return v_bs_4724_;
}
else
{
lean_object* v_v_4726_; lean_object* v___x_4727_; lean_object* v_bs_x27_4728_; lean_object* v___x_4729_; size_t v___x_4730_; size_t v___x_4731_; lean_object* v___x_4732_; 
v_v_4726_ = lean_array_uget(v_bs_4724_, v_i_4723_);
v___x_4727_ = lean_unsigned_to_nat(0u);
v_bs_x27_4728_ = lean_array_uset(v_bs_4724_, v_i_4723_, v___x_4727_);
v___x_4729_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4726_);
v___x_4730_ = ((size_t)1ULL);
v___x_4731_ = lean_usize_add(v_i_4723_, v___x_4730_);
v___x_4732_ = lean_array_uset(v_bs_x27_4728_, v_i_4723_, v___x_4729_);
v_i_4723_ = v___x_4731_;
v_bs_4724_ = v___x_4732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4734_, lean_object* v_i_4735_, lean_object* v_bs_4736_){
_start:
{
size_t v_sz_boxed_4737_; size_t v_i_boxed_4738_; lean_object* v_res_4739_; 
v_sz_boxed_4737_ = lean_unbox_usize(v_sz_4734_);
lean_dec(v_sz_4734_);
v_i_boxed_4738_ = lean_unbox_usize(v_i_4735_);
lean_dec(v_i_4735_);
v_res_4739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4737_, v_i_boxed_4738_, v_bs_4736_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4740_){
_start:
{
size_t v_sz_4741_; size_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v_sz_4741_ = lean_array_size(v_a_4740_);
v___x_4742_ = ((size_t)0ULL);
v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4741_, v___x_4742_, v_a_4740_);
v___x_4744_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4745_, size_t v_i_4746_, lean_object* v_bs_4747_){
_start:
{
uint8_t v___x_4748_; 
v___x_4748_ = lean_usize_dec_lt(v_i_4746_, v_sz_4745_);
if (v___x_4748_ == 0)
{
return v_bs_4747_;
}
else
{
lean_object* v_v_4749_; lean_object* v___x_4750_; lean_object* v_bs_x27_4751_; lean_object* v___x_4752_; size_t v___x_4753_; size_t v___x_4754_; lean_object* v___x_4755_; 
v_v_4749_ = lean_array_uget(v_bs_4747_, v_i_4746_);
v___x_4750_ = lean_unsigned_to_nat(0u);
v_bs_x27_4751_ = lean_array_uset(v_bs_4747_, v_i_4746_, v___x_4750_);
v___x_4752_ = l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4749_);
v___x_4753_ = ((size_t)1ULL);
v___x_4754_ = lean_usize_add(v_i_4746_, v___x_4753_);
v___x_4755_ = lean_array_uset(v_bs_x27_4751_, v_i_4746_, v___x_4752_);
v_i_4746_ = v___x_4754_;
v_bs_4747_ = v___x_4755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4757_, lean_object* v_i_4758_, lean_object* v_bs_4759_){
_start:
{
size_t v_sz_boxed_4760_; size_t v_i_boxed_4761_; lean_object* v_res_4762_; 
v_sz_boxed_4760_ = lean_unbox_usize(v_sz_4757_);
lean_dec(v_sz_4757_);
v_i_boxed_4761_ = lean_unbox_usize(v_i_4758_);
lean_dec(v_i_4758_);
v_res_4762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4760_, v_i_boxed_4761_, v_bs_4759_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4763_){
_start:
{
size_t v_sz_4764_; size_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v_sz_4764_ = lean_array_size(v_a_4763_);
v___x_4765_ = ((size_t)0ULL);
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4764_, v___x_4765_, v_a_4763_);
v___x_4767_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4768_){
_start:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4769_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4770_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4768_);
v___x_4771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4769_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = lean_box(0);
v___x_4773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
lean_ctor_set(v___x_4774_, 1, v___x_4772_);
v___x_4775_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4776_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4774_, v___x_4775_);
v___x_4777_ = l_Lean_Json_mkObj(v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = 1;
v___x_4790_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4790_, v___x_4789_);
return v___x_4791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4794_ = lean_string_append(v___x_4793_, v___x_4792_);
return v___x_4794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4795_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4797_ = lean_string_append(v___x_4796_, v___x_4795_);
return v___x_4797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4798_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4799_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4800_ = lean_string_append(v___x_4799_, v___x_4798_);
return v___x_4800_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4803_ = lean_string_append(v___x_4802_, v___x_4801_);
return v___x_4803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4805_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4806_ = lean_string_append(v___x_4805_, v___x_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4807_){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4807_);
v___x_4809_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4807_, v___x_4808_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4819_; 
lean_dec(v_json_4807_);
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4819_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4819_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4817_; 
v___x_4814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4815_ = lean_string_append(v___x_4814_, v_a_4810_);
lean_dec(v_a_4810_);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4815_);
v___x_4817_ = v___x_4812_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4815_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
else
{
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_dec(v_json_4807_);
v_a_4820_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4809_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4809_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
lean_ctor_set_tag(v___x_4822_, 0);
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v_a_4828_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4828_);
lean_dec_ref(v___x_4809_);
v___x_4829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4807_, v___x_4829_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4840_; 
lean_dec(v_a_4828_);
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4840_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4840_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4835_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4836_ = lean_string_append(v___x_4835_, v_a_4831_);
lean_dec(v_a_4831_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4836_);
v___x_4838_ = v___x_4833_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec(v_a_4828_);
v_a_4841_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4830_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4830_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
lean_ctor_set_tag(v___x_4843_, 0);
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4857_; 
v_a_4849_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4851_ = v___x_4830_;
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4830_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4857_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v_a_4828_);
lean_ctor_set(v___x_4853_, 1, v_a_4849_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4853_);
v___x_4855_ = v___x_4851_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4860_){
_start:
{
lean_object* v_module_4861_; lean_object* v_decl_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4885_; 
v_module_4861_ = lean_ctor_get(v_x_4860_, 0);
v_decl_4862_ = lean_ctor_get(v_x_4860_, 1);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_x_4860_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4864_ = v_x_4860_;
v_isShared_4865_ = v_isSharedCheck_4885_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_decl_4862_);
lean_inc(v_module_4861_);
lean_dec(v_x_4860_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4885_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4866_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4867_ = 1;
v___x_4868_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4861_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 1, v___x_4869_);
lean_ctor_set(v___x_4864_, 0, v___x_4866_);
v___x_4871_ = v___x_4864_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4872_ = lean_box(0);
v___x_4873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4875_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4862_, v___x_4867_);
v___x_4876_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
v___x_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4874_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set(v___x_4878_, 1, v___x_4872_);
v___x_4879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
lean_ctor_set(v___x_4879_, 1, v___x_4872_);
v___x_4880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4873_);
lean_ctor_set(v___x_4880_, 1, v___x_4879_);
v___x_4881_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4882_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4880_, v___x_4881_);
v___x_4883_ = l_Lean_Json_mkObj(v___x_4882_);
return v___x_4883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4888_, lean_object* v_k_4889_){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = l_Lean_Json_getObjValD(v_j_4888_, v_k_4889_);
v___x_4891_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4890_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4892_, lean_object* v_k_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4892_, v_k_4893_);
lean_dec_ref(v_k_4893_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4897_){
_start:
{
if (lean_obj_tag(v_x_4897_) == 0)
{
lean_object* v___x_4898_; 
v___x_4898_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4898_;
}
else
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4897_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
else
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4916_; 
v_a_4908_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4910_ = v___x_4899_;
v_isShared_4911_ = v_isSharedCheck_4916_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4899_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4916_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_a_4908_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4912_);
v___x_4914_ = v___x_4910_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4912_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4917_, lean_object* v_k_4918_){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4919_ = l_Lean_Json_getObjValD(v_j_4917_, v_k_4918_);
v___x_4920_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4919_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4921_, lean_object* v_k_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4921_, v_k_4922_);
lean_dec_ref(v_k_4922_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4926_){
_start:
{
if (lean_obj_tag(v_x_4926_) == 0)
{
lean_object* v___x_4927_; 
v___x_4927_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4927_;
}
else
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4926_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4928_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4928_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4945_; 
v_a_4937_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4945_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4945_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4941_, 0, v_a_4937_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4941_);
v___x_4943_ = v___x_4939_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4941_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4946_, lean_object* v_k_4947_){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = l_Lean_Json_getObjValD(v_j_4946_, v_k_4947_);
v___x_4949_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4950_, lean_object* v_k_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4950_, v_k_4951_);
lean_dec_ref(v_k_4951_);
return v_res_4952_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4959_ = 1;
v___x_4960_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4961_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4960_, v___x_4959_);
return v___x_4961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4962_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4964_ = lean_string_append(v___x_4963_, v___x_4962_);
return v___x_4964_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = 1;
v___x_4969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4970_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4969_, v___x_4968_);
return v___x_4970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4973_ = lean_string_append(v___x_4972_, v___x_4971_);
return v___x_4973_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4976_ = lean_string_append(v___x_4975_, v___x_4974_);
return v___x_4976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4980_ = 1;
v___x_4981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4981_, v___x_4980_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4983_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4985_ = lean_string_append(v___x_4984_, v___x_4983_);
return v___x_4985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4988_ = lean_string_append(v___x_4987_, v___x_4986_);
return v___x_4988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = 1;
v___x_4993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4993_, v___x_4992_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4995_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4997_ = lean_string_append(v___x_4996_, v___x_4995_);
return v___x_4997_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4998_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_5000_ = lean_string_append(v___x_4999_, v___x_4998_);
return v___x_5000_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = 1;
v___x_5005_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_5006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5005_, v___x_5004_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5007_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_5008_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5009_ = lean_string_append(v___x_5008_, v___x_5007_);
return v___x_5009_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5011_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_5012_ = lean_string_append(v___x_5011_, v___x_5010_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = 1;
v___x_5018_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_5019_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5018_, v___x_5017_);
return v___x_5019_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_5021_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5022_ = lean_string_append(v___x_5021_, v___x_5020_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5023_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5024_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5025_ = lean_string_append(v___x_5024_, v___x_5023_);
return v___x_5025_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5029_ = 1;
v___x_5030_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5031_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5030_, v___x_5029_);
return v___x_5031_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5032_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5033_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5034_ = lean_string_append(v___x_5033_, v___x_5032_);
return v___x_5034_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5035_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5036_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5037_ = lean_string_append(v___x_5036_, v___x_5035_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5038_){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5039_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5038_);
v___x_5040_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5038_, v___x_5039_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5050_; 
lean_dec(v_json_5038_);
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5043_ = v___x_5040_;
v_isShared_5044_ = v_isSharedCheck_5050_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5040_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5050_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5045_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5046_ = lean_string_append(v___x_5045_, v_a_5041_);
lean_dec(v_a_5041_);
if (v_isShared_5044_ == 0)
{
lean_ctor_set(v___x_5043_, 0, v___x_5046_);
v___x_5048_ = v___x_5043_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
else
{
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5058_; 
lean_dec(v_json_5038_);
v_a_5051_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5053_ = v___x_5040_;
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5040_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set_tag(v___x_5053_, 0);
v___x_5056_ = v___x_5053_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v_a_5059_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5059_);
lean_dec_ref(v___x_5040_);
v___x_5060_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5038_);
v___x_5061_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5038_, v___x_5060_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5071_; 
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5064_ = v___x_5061_;
v_isShared_5065_ = v_isSharedCheck_5071_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5061_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5071_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5066_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5067_ = lean_string_append(v___x_5066_, v_a_5062_);
lean_dec(v_a_5062_);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v___x_5067_);
v___x_5069_ = v___x_5064_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
else
{
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5072_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5061_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5061_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
lean_ctor_set_tag(v___x_5074_, 0);
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v_a_5080_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5080_);
lean_dec_ref(v___x_5061_);
v___x_5081_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5038_);
v___x_5082_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5038_, v___x_5081_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5085_ = v___x_5082_;
v_isShared_5086_ = v_isSharedCheck_5092_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5082_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5092_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5090_; 
v___x_5087_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5088_ = lean_string_append(v___x_5087_, v_a_5083_);
lean_dec(v_a_5083_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set(v___x_5085_, 0, v___x_5088_);
v___x_5090_ = v___x_5085_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
else
{
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5093_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5082_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5082_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 0);
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v_a_5101_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5101_);
lean_dec_ref(v___x_5082_);
v___x_5102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5038_);
v___x_5103_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5038_, v___x_5102_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5113_; 
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5106_ = v___x_5103_;
v_isShared_5107_ = v_isSharedCheck_5113_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5103_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5113_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5111_; 
v___x_5108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5109_ = lean_string_append(v___x_5108_, v_a_5104_);
lean_dec(v_a_5104_);
if (v_isShared_5107_ == 0)
{
lean_ctor_set(v___x_5106_, 0, v___x_5109_);
v___x_5111_ = v___x_5106_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5109_);
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
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5114_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5103_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5103_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set_tag(v___x_5116_, 0);
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v_a_5122_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5122_);
lean_dec_ref(v___x_5103_);
v___x_5123_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5038_);
v___x_5124_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5038_, v___x_5123_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5134_; 
lean_dec(v_a_5122_);
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5134_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5134_ == 0)
{
v___x_5127_ = v___x_5124_;
v_isShared_5128_ = v_isSharedCheck_5134_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5124_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5134_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5129_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5130_ = lean_string_append(v___x_5129_, v_a_5125_);
lean_dec(v_a_5125_);
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 0, v___x_5130_);
v___x_5132_ = v___x_5127_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5130_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
else
{
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_dec(v_a_5122_);
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
lean_dec(v_json_5038_);
v_a_5135_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5124_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5124_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
lean_ctor_set_tag(v___x_5137_, 0);
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v_a_5143_ = lean_ctor_get(v___x_5124_, 0);
lean_inc(v_a_5143_);
lean_dec_ref(v___x_5124_);
v___x_5144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5145_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5038_, v___x_5144_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5155_; 
lean_dec(v_a_5143_);
lean_dec(v_a_5122_);
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5148_ = v___x_5145_;
v_isShared_5149_ = v_isSharedCheck_5155_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5145_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5155_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5151_ = lean_string_append(v___x_5150_, v_a_5146_);
lean_dec(v_a_5146_);
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v___x_5151_);
v___x_5153_ = v___x_5148_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
else
{
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec(v_a_5143_);
lean_dec(v_a_5122_);
lean_dec(v_a_5101_);
lean_dec(v_a_5080_);
lean_dec(v_a_5059_);
v_a_5156_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5145_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5145_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
lean_ctor_set_tag(v___x_5158_, 0);
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5174_; 
v_a_5164_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5166_ = v___x_5145_;
v_isShared_5167_ = v_isSharedCheck_5174_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5145_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5174_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; lean_object* v___x_5172_; 
v___x_5168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5168_, 0, v_a_5059_);
lean_ctor_set(v___x_5168_, 1, v_a_5080_);
lean_ctor_set(v___x_5168_, 2, v_a_5101_);
lean_ctor_set(v___x_5168_, 3, v_a_5122_);
v___x_5169_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5169_, 0, v___x_5168_);
lean_ctor_set(v___x_5169_, 1, v_a_5143_);
v___x_5170_ = lean_unbox(v_a_5164_);
lean_dec(v_a_5164_);
lean_ctor_set_uint8(v___x_5169_, sizeof(void*)*2, v___x_5170_);
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 0, v___x_5169_);
v___x_5172_ = v___x_5166_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5169_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5177_, lean_object* v_x_5178_){
_start:
{
if (lean_obj_tag(v_x_5178_) == 0)
{
lean_object* v___x_5179_; 
lean_dec_ref(v_k_5177_);
v___x_5179_ = lean_box(0);
return v___x_5179_;
}
else
{
lean_object* v_val_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
v_val_5180_ = lean_ctor_get(v_x_5178_, 0);
lean_inc(v_val_5180_);
lean_dec_ref(v_x_5178_);
v___x_5181_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5180_);
v___x_5182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5182_, 0, v_k_5177_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
v___x_5183_ = lean_box(0);
v___x_5184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
return v___x_5184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5185_, lean_object* v_x_5186_){
_start:
{
if (lean_obj_tag(v_x_5186_) == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref(v_k_5185_);
v___x_5187_ = lean_box(0);
return v___x_5187_;
}
else
{
lean_object* v_val_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v_val_5188_ = lean_ctor_get(v_x_5186_, 0);
lean_inc(v_val_5188_);
lean_dec_ref(v_x_5186_);
v___x_5189_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5188_);
v___x_5190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5190_, 0, v_k_5185_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = lean_box(0);
v___x_5192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5190_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
return v___x_5192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5193_){
_start:
{
lean_object* v_toLocationLink_5194_; lean_object* v_ident_x3f_5195_; uint8_t v_isDefault_5196_; lean_object* v_originSelectionRange_x3f_5197_; lean_object* v_targetUri_5198_; lean_object* v_targetRange_5199_; lean_object* v_targetSelectionRange_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v_toLocationLink_5194_ = lean_ctor_get(v_x_5193_, 0);
lean_inc_ref(v_toLocationLink_5194_);
v_ident_x3f_5195_ = lean_ctor_get(v_x_5193_, 1);
lean_inc(v_ident_x3f_5195_);
v_isDefault_5196_ = lean_ctor_get_uint8(v_x_5193_, sizeof(void*)*2);
lean_dec_ref(v_x_5193_);
v_originSelectionRange_x3f_5197_ = lean_ctor_get(v_toLocationLink_5194_, 0);
lean_inc(v_originSelectionRange_x3f_5197_);
v_targetUri_5198_ = lean_ctor_get(v_toLocationLink_5194_, 1);
lean_inc_ref(v_targetUri_5198_);
v_targetRange_5199_ = lean_ctor_get(v_toLocationLink_5194_, 2);
lean_inc_ref(v_targetRange_5199_);
v_targetSelectionRange_5200_ = lean_ctor_get(v_toLocationLink_5194_, 3);
lean_inc_ref(v_targetSelectionRange_5200_);
lean_dec_ref(v_toLocationLink_5194_);
v___x_5201_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5202_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5201_, v_originSelectionRange_x3f_5197_);
v___x_5203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5204_, 0, v_targetUri_5198_);
v___x_5205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5203_);
lean_ctor_set(v___x_5205_, 1, v___x_5204_);
v___x_5206_ = lean_box(0);
v___x_5207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5205_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5209_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5199_);
v___x_5210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5208_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
v___x_5211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5210_);
lean_ctor_set(v___x_5211_, 1, v___x_5206_);
v___x_5212_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5213_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5200_);
v___x_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5212_);
lean_ctor_set(v___x_5214_, 1, v___x_5213_);
v___x_5215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5214_);
lean_ctor_set(v___x_5215_, 1, v___x_5206_);
v___x_5216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5217_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5216_, v_ident_x3f_5195_);
v___x_5218_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5219_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5219_, 0, v_isDefault_5196_);
v___x_5220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5218_);
lean_ctor_set(v___x_5220_, 1, v___x_5219_);
v___x_5221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5220_);
lean_ctor_set(v___x_5221_, 1, v___x_5206_);
v___x_5222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
lean_ctor_set(v___x_5222_, 1, v___x_5206_);
v___x_5223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5217_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
v___x_5224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5215_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5211_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
v___x_5226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5207_);
lean_ctor_set(v___x_5226_, 1, v___x_5225_);
v___x_5227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5202_);
lean_ctor_set(v___x_5227_, 1, v___x_5226_);
v___x_5228_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5229_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5227_, v___x_5228_);
v___x_5230_ = l_Lean_Json_mkObj(v___x_5229_);
return v___x_5230_;
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

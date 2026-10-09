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
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl___boxed(lean_object*);
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
uint8_t l_Lean_Lsp_instBEqRefIdent_beq(lean_object* v_x_137_, lean_object* v_x_138_){
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
LEAN_EXPORT void l_Lean_Lsp_instBEqRefIdent_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_137_ = stack[0].m_obj;
lean_object* v_x_138_ = stack[1].m_obj;
uint8_t v_res_156_;
v_res_156_ = l_Lean_Lsp_instBEqRefIdent_beq(v_x_137_, v_x_138_);
stack->m_num = v_res_156_;
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
uint64_t l_Lean_Lsp_instHashableRefIdent_hash(lean_object* v_x_163_){
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
LEAN_EXPORT void l_Lean_Lsp_instHashableRefIdent_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_163_ = stack[0].m_obj;
uint64_t v_res_178_;
v_res_178_ = l_Lean_Lsp_instHashableRefIdent_hash(v_x_163_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRefIdent_hash___boxed(lean_object* v_x_179_){
_start:
{
uint64_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_Lsp_instHashableRefIdent_hash(v_x_179_);
lean_dec_ref(v_x_179_);
v_r_181_ = lean_box_uint64(v_res_180_);
return v_r_181_;
}
}
uint8_t l_Lean_Lsp_instOrdRefIdent_ord(lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v_b_193_; lean_object* v_b_194_; 
if (lean_obj_tag(v_x_188_) == 0)
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v_moduleName_197_; lean_object* v_identName_198_; lean_object* v_moduleName_199_; lean_object* v_identName_200_; 
v_moduleName_197_ = lean_ctor_get(v_x_188_, 0);
v_identName_198_ = lean_ctor_get(v_x_188_, 1);
v_moduleName_199_ = lean_ctor_get(v_x_189_, 0);
v_identName_200_ = lean_ctor_get(v_x_189_, 1);
v_a_191_ = v_moduleName_197_;
v_a_192_ = v_identName_198_;
v_b_193_ = v_moduleName_199_;
v_b_194_ = v_identName_200_;
goto v___jp_190_;
}
else
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
}
else
{
if (lean_obj_tag(v_x_189_) == 0)
{
uint8_t v___x_202_; 
v___x_202_ = 2;
return v___x_202_;
}
else
{
lean_object* v_moduleName_203_; lean_object* v_id_204_; lean_object* v_moduleName_205_; lean_object* v_id_206_; 
v_moduleName_203_ = lean_ctor_get(v_x_188_, 0);
v_id_204_ = lean_ctor_get(v_x_188_, 1);
v_moduleName_205_ = lean_ctor_get(v_x_189_, 0);
v_id_206_ = lean_ctor_get(v_x_189_, 1);
v_a_191_ = v_moduleName_203_;
v_a_192_ = v_id_204_;
v_b_193_ = v_moduleName_205_;
v_b_194_ = v_id_206_;
goto v___jp_190_;
}
}
v___jp_190_:
{
uint8_t v___x_195_; 
v___x_195_ = lean_string_compare(v_a_191_, v_b_193_);
if (v___x_195_ == 1)
{
uint8_t v___x_196_; 
v___x_196_ = lean_string_compare(v_a_192_, v_b_194_);
return v___x_196_;
}
else
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instOrdRefIdent_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_188_ = stack[0].m_obj;
lean_object* v_x_189_ = stack[1].m_obj;
uint8_t v_res_207_;
v_res_207_ = l_Lean_Lsp_instOrdRefIdent_ord(v_x_188_, v_x_189_);
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRefIdent_ord___boxed(lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Lsp_instOrdRefIdent_ord(v_x_208_, v_x_209_);
lean_dec_ref(v_x_209_);
lean_dec_ref(v_x_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl(lean_object* v_x_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_tag_nat(v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl___boxed(lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl(v_x_216_);
lean_dec_ref(v_x_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(lean_object* v_t_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_m_220_; lean_object* v_n_221_; lean_object* v___x_222_; 
v_m_220_ = lean_ctor_get(v_t_218_, 0);
lean_inc_ref(v_m_220_);
v_n_221_ = lean_ctor_get(v_t_218_, 1);
lean_inc_ref(v_n_221_);
lean_dec_ref(v_t_218_);
v___x_222_ = lean_apply_2(v_k_219_, v_m_220_, v_n_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_225_, v_k_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___boxed(lean_object* v_motive_229_, lean_object* v_ctorIdx_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_k_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(v_motive_229_, v_ctorIdx_230_, v_t_231_, v_h_232_, v_k_233_);
lean_dec(v_ctorIdx_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim___redArg(lean_object* v_t_235_, lean_object* v_c_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_235_, v_c_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim(lean_object* v_motive_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_c_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_239_, v_c_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim___redArg(lean_object* v_t_243_, lean_object* v_f_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_243_, v_f_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim(lean_object* v_motive_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_f_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_247_, v_f_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(lean_object* v_json_284_){
_start:
{
lean_object* v___x_285_; 
lean_inc(v_json_284_);
v___x_285_ = l_Lean_Json_getTag_x3f(v_json_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; 
lean_dec(v_json_284_);
v___x_286_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1));
return v___x_286_;
}
else
{
lean_object* v_val_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_val_287_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_285_, 1);
v___x_288_ = lean_box(0);
v___x_289_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_290_ = lean_string_dec_eq(v_val_287_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_292_ = lean_string_dec_eq(v_val_287_, v___x_291_);
lean_dec(v_val_287_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_json_284_);
v___x_293_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5));
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(2u);
v___x_295_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11));
v___x_296_ = l_Lean_Json_parseCtorFields(v_json_284_, v___x_291_, v___x_294_, v___x_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_305_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_296_, 1);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_array_get_borrowed(v___x_288_, v_a_305_, v___x_306_);
lean_inc(v___x_307_);
v___x_308_ = l_Lean_Json_getStr_x3f(v___x_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_a_305_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_317_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_308_, 1);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_array_get(v___x_288_, v_a_305_, v___x_318_);
lean_dec(v_a_305_);
v___x_320_ = l_Lean_Json_getStr_x3f(v___x_319_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_a_317_);
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
v_a_329_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v___x_320_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_320_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_a_317_);
lean_ctor_set(v___x_333_, 1, v_a_329_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_val_287_);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15));
v___x_340_ = l_Lean_Json_parseCtorFields(v_json_284_, v___x_289_, v___x_338_, v___x_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_349_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_340_, 1);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_array_get_borrowed(v___x_288_, v_a_349_, v___x_350_);
lean_inc(v___x_351_);
v___x_352_ = l_Lean_Json_getStr_x3f(v___x_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_a_349_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_a_361_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_352_, 1);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_array_get(v___x_288_, v_a_349_, v___x_362_);
lean_dec(v_a_349_);
v___x_364_ = l_Lean_Json_getStr_x3f(v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_a_361_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_a_373_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v___x_364_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_364_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v_a_361_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v_m_385_; lean_object* v_n_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_406_; 
v_m_385_ = lean_ctor_get(v_x_384_, 0);
v_n_386_ = lean_ctor_get(v_x_384_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_406_ == 0)
{
v___x_388_ = v_x_384_;
v_isShared_389_ = v_isSharedCheck_406_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_n_386_);
lean_inc(v_m_385_);
lean_dec(v_x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_406_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_391_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_392_, 0, v_m_385_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_392_);
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_392_);
v___x_394_ = v_reuseFailAlloc_405_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_395_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8));
v___x_396_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_396_, 0, v_n_386_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_394_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_Json_mkObj(v___x_400_);
lean_dec_ref_known(v___x_400_, 2);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_390_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_398_);
v___x_404_ = l_Lean_Json_mkObj(v___x_403_);
lean_dec_ref_known(v___x_403_, 2);
return v___x_404_;
}
}
}
else
{
lean_object* v_m_407_; lean_object* v_i_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_428_; 
v_m_407_ = lean_ctor_get(v_x_384_, 0);
v_i_408_ = lean_ctor_get(v_x_384_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_428_ == 0)
{
v___x_410_ = v_x_384_;
v_isShared_411_ = v_isSharedCheck_428_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_i_408_);
lean_inc(v_m_407_);
lean_dec(v_x_384_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_428_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_412_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_413_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v_m_407_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 0);
lean_ctor_set(v___x_410_, 1, v___x_414_);
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_414_);
v___x_416_ = v_reuseFailAlloc_427_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_417_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12));
v___x_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_418_, 0, v_i_408_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_416_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Json_mkObj(v___x_422_);
lean_dec_ref_known(v___x_422_, 2);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_412_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_420_);
v___x_426_ = l_Lean_Json_mkObj(v___x_425_);
lean_dec_ref_known(v___x_425_, 2);
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v_moduleName_432_; lean_object* v_identName_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_moduleName_432_ = lean_ctor_get(v_x_431_, 0);
v_identName_433_ = lean_ctor_get(v_x_431_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v_x_431_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_identName_433_);
lean_inc(v_moduleName_432_);
lean_dec(v_x_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_moduleName_432_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_identName_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_moduleName_441_; lean_object* v_id_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_moduleName_441_ = lean_ctor_get(v_x_431_, 0);
v_id_442_ = lean_ctor_get(v_x_431_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_x_431_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_id_442_);
lean_inc(v_moduleName_441_);
lean_dec(v_x_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_moduleName_441_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_id_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v_m_451_; lean_object* v_n_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_m_451_ = lean_ctor_get(v_x_450_, 0);
v_n_452_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v_x_450_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_n_452_);
lean_inc(v_m_451_);
lean_dec(v_x_450_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_m_451_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_n_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_m_460_; lean_object* v_i_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_m_460_ = lean_ctor_get(v_x_450_, 0);
v_i_461_ = lean_ctor_get(v_x_450_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_x_450_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v_x_450_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_i_461_);
lean_inc(v_m_460_);
lean_dec(v_x_450_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_m_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_i_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* v_s_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(v_s_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_a_479_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_470_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_470_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_Lsp_RefIdent_fromJsonRepr(v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* v_id_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = l_Lean_Lsp_RefIdent_toJsonRepr(v_id_488_);
v___x_490_ = l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object* v_r_495_){
_start:
{
lean_object* v_range_496_; lean_object* v_pos_497_; lean_object* v_endPos_498_; lean_object* v_selectionRange_499_; lean_object* v_pos_500_; lean_object* v_endPos_501_; lean_object* v_charUtf16_502_; lean_object* v_endCharUtf16_503_; lean_object* v_line_504_; lean_object* v_line_505_; lean_object* v_charUtf16_506_; lean_object* v_endCharUtf16_507_; lean_object* v_line_508_; lean_object* v_line_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_range_496_ = lean_ctor_get(v_r_495_, 0);
v_pos_497_ = lean_ctor_get(v_range_496_, 0);
v_endPos_498_ = lean_ctor_get(v_range_496_, 2);
v_selectionRange_499_ = lean_ctor_get(v_r_495_, 1);
v_pos_500_ = lean_ctor_get(v_selectionRange_499_, 0);
v_endPos_501_ = lean_ctor_get(v_selectionRange_499_, 2);
v_charUtf16_502_ = lean_ctor_get(v_range_496_, 1);
v_endCharUtf16_503_ = lean_ctor_get(v_range_496_, 3);
v_line_504_ = lean_ctor_get(v_pos_497_, 0);
v_line_505_ = lean_ctor_get(v_endPos_498_, 0);
v_charUtf16_506_ = lean_ctor_get(v_selectionRange_499_, 1);
v_endCharUtf16_507_ = lean_ctor_get(v_selectionRange_499_, 3);
v_line_508_ = lean_ctor_get(v_pos_500_, 0);
v_line_509_ = lean_ctor_get(v_endPos_501_, 0);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_sub(v_line_504_, v___x_510_);
v___x_512_ = lean_nat_sub(v_line_505_, v___x_510_);
v___x_513_ = lean_nat_sub(v_line_508_, v___x_510_);
v___x_514_ = lean_nat_sub(v_line_509_, v___x_510_);
lean_inc(v_endCharUtf16_507_);
lean_inc(v_charUtf16_506_);
lean_inc(v_endCharUtf16_503_);
lean_inc(v_charUtf16_502_);
v___x_515_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_515_, 0, v___x_511_);
lean_ctor_set(v___x_515_, 1, v_charUtf16_502_);
lean_ctor_set(v___x_515_, 2, v___x_512_);
lean_ctor_set(v___x_515_, 3, v_endCharUtf16_503_);
lean_ctor_set(v___x_515_, 4, v___x_513_);
lean_ctor_set(v___x_515_, 5, v_charUtf16_506_);
lean_ctor_set(v___x_515_, 6, v___x_514_);
lean_ctor_set(v___x_515_, 7, v_endCharUtf16_507_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object* v_r_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_r_516_);
lean_dec_ref(v_r_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object* v_i_518_){
_start:
{
lean_object* v_rangeStartPosLine_519_; lean_object* v_rangeStartPosCharacter_520_; lean_object* v_rangeEndPosLine_521_; lean_object* v_rangeEndPosCharacter_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_rangeStartPosLine_519_ = lean_ctor_get(v_i_518_, 0);
v_rangeStartPosCharacter_520_ = lean_ctor_get(v_i_518_, 1);
v_rangeEndPosLine_521_ = lean_ctor_get(v_i_518_, 2);
v_rangeEndPosCharacter_522_ = lean_ctor_get(v_i_518_, 3);
lean_inc(v_rangeStartPosCharacter_520_);
lean_inc(v_rangeStartPosLine_519_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_rangeStartPosLine_519_);
lean_ctor_set(v___x_523_, 1, v_rangeStartPosCharacter_520_);
lean_inc(v_rangeEndPosCharacter_522_);
lean_inc(v_rangeEndPosLine_521_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_rangeEndPosLine_521_);
lean_ctor_set(v___x_524_, 1, v_rangeEndPosCharacter_522_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object* v_i_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Lsp_DeclInfo_range(v_i_526_);
lean_dec_ref(v_i_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object* v_i_528_){
_start:
{
lean_object* v_selectionRangeStartPosLine_529_; lean_object* v_selectionRangeStartPosCharacter_530_; lean_object* v_selectionRangeEndPosLine_531_; lean_object* v_selectionRangeEndPosCharacter_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_selectionRangeStartPosLine_529_ = lean_ctor_get(v_i_528_, 4);
v_selectionRangeStartPosCharacter_530_ = lean_ctor_get(v_i_528_, 5);
v_selectionRangeEndPosLine_531_ = lean_ctor_get(v_i_528_, 6);
v_selectionRangeEndPosCharacter_532_ = lean_ctor_get(v_i_528_, 7);
lean_inc(v_selectionRangeStartPosCharacter_530_);
lean_inc(v_selectionRangeStartPosLine_529_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_selectionRangeStartPosLine_529_);
lean_ctor_set(v___x_533_, 1, v_selectionRangeStartPosCharacter_530_);
lean_inc(v_selectionRangeEndPosCharacter_532_);
lean_inc(v_selectionRangeEndPosLine_531_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_selectionRangeEndPosLine_531_);
lean_ctor_set(v___x_534_, 1, v_selectionRangeEndPosCharacter_532_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object* v_i_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Lsp_DeclInfo_selectionRange(v_i_536_);
lean_dec_ref(v_i_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object* v_i_538_){
_start:
{
lean_object* v_rangeStartPosLine_539_; lean_object* v_rangeStartPosCharacter_540_; lean_object* v_rangeEndPosLine_541_; lean_object* v_rangeEndPosCharacter_542_; lean_object* v_selectionRangeStartPosLine_543_; lean_object* v_selectionRangeStartPosCharacter_544_; lean_object* v_selectionRangeEndPosLine_545_; lean_object* v_selectionRangeEndPosCharacter_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_rangeStartPosLine_539_ = lean_ctor_get(v_i_538_, 0);
lean_inc(v_rangeStartPosLine_539_);
v_rangeStartPosCharacter_540_ = lean_ctor_get(v_i_538_, 1);
lean_inc(v_rangeStartPosCharacter_540_);
v_rangeEndPosLine_541_ = lean_ctor_get(v_i_538_, 2);
lean_inc(v_rangeEndPosLine_541_);
v_rangeEndPosCharacter_542_ = lean_ctor_get(v_i_538_, 3);
lean_inc(v_rangeEndPosCharacter_542_);
v_selectionRangeStartPosLine_543_ = lean_ctor_get(v_i_538_, 4);
lean_inc(v_selectionRangeStartPosLine_543_);
v_selectionRangeStartPosCharacter_544_ = lean_ctor_get(v_i_538_, 5);
lean_inc(v_selectionRangeStartPosCharacter_544_);
v_selectionRangeEndPosLine_545_ = lean_ctor_get(v_i_538_, 6);
lean_inc(v_selectionRangeEndPosLine_545_);
v_selectionRangeEndPosCharacter_546_ = lean_ctor_get(v_i_538_, 7);
lean_inc(v_selectionRangeEndPosCharacter_546_);
lean_dec_ref(v_i_538_);
v___x_547_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_539_);
v___x_548_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_540_);
v___x_550_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
v___x_551_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_541_);
v___x_552_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v___x_553_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_542_);
v___x_554_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___x_555_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_543_);
v___x_556_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_544_);
v___x_558_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_545_);
v___x_560_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
v___x_561_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_546_);
v___x_562_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = lean_unsigned_to_nat(8u);
v___x_564_ = lean_mk_empty_array_with_capacity(v___x_563_);
v___x_565_ = lean_array_push(v___x_564_, v___x_548_);
v___x_566_ = lean_array_push(v___x_565_, v___x_550_);
v___x_567_ = lean_array_push(v___x_566_, v___x_552_);
v___x_568_ = lean_array_push(v___x_567_, v___x_554_);
v___x_569_ = lean_array_push(v___x_568_, v___x_556_);
v___x_570_ = lean_array_push(v___x_569_, v___x_558_);
v___x_571_ = lean_array_push(v___x_570_, v___x_560_);
v___x_572_ = lean_array_push(v___x_571_, v___x_562_);
v___x_573_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object* v___x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 4)
{
lean_object* v_elems_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_699_; 
v_elems_582_ = lean_ctor_get(v_x_581_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_699_ == 0)
{
v___x_584_ = v_x_581_;
v_isShared_585_ = v_isSharedCheck_699_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_elems_582_);
lean_dec(v_x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_699_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_array_get_size(v_elems_582_);
v___x_587_ = lean_unsigned_to_nat(8u);
v___x_588_ = lean_nat_dec_eq(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec_ref(v_elems_582_);
v___x_589_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_590_ = l_Nat_reprFast(v___x_586_);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
lean_dec_ref(v___x_590_);
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 0);
lean_ctor_set(v___x_584_, 0, v___x_591_);
v___x_593_ = v___x_584_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_584_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_595_);
lean_inc(v___x_596_);
v___x_597_ = l_Lean_Json_getNat_x3f(v___x_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_elems_582_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_a_606_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_597_, 1);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_607_);
lean_inc(v___x_608_);
v___x_609_ = l_Lean_Json_getNat_x3f(v___x_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_618_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_609_, 1);
v___x_619_ = lean_unsigned_to_nat(2u);
v___x_620_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_619_);
lean_inc(v___x_620_);
v___x_621_ = l_Lean_Json_getNat_x3f(v___x_620_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_618_);
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v_a_630_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_621_, 1);
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_631_);
lean_inc(v___x_632_);
v___x_633_ = l_Lean_Json_getNat_x3f(v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_a_630_);
lean_dec(v_a_618_);
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_a_642_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_633_, 1);
v___x_643_ = lean_unsigned_to_nat(4u);
v___x_644_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_643_);
lean_inc(v___x_644_);
v___x_645_ = l_Lean_Json_getNat_x3f(v___x_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_642_);
lean_dec(v_a_630_);
lean_dec(v_a_618_);
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_645_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_645_, 1);
v___x_655_ = lean_unsigned_to_nat(5u);
v___x_656_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_655_);
lean_inc(v___x_656_);
v___x_657_ = l_Lean_Json_getNat_x3f(v___x_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_a_654_);
lean_dec(v_a_642_);
lean_dec(v_a_630_);
lean_dec(v_a_618_);
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_666_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_657_, 1);
v___x_667_ = lean_unsigned_to_nat(6u);
v___x_668_ = lean_array_get_borrowed(v___x_580_, v_elems_582_, v___x_667_);
lean_inc(v___x_668_);
v___x_669_ = l_Lean_Json_getNat_x3f(v___x_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_666_);
lean_dec(v_a_654_);
lean_dec(v_a_642_);
lean_dec(v_a_630_);
lean_dec(v_a_618_);
lean_dec(v_a_606_);
lean_dec_ref(v_elems_582_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_a_678_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_669_, 1);
v___x_679_ = lean_unsigned_to_nat(7u);
v___x_680_ = lean_array_get(v___x_580_, v_elems_582_, v___x_679_);
lean_dec_ref(v_elems_582_);
v___x_681_ = l_Lean_Json_getNat_x3f(v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_678_);
lean_dec(v_a_666_);
lean_dec(v_a_654_);
lean_dec(v_a_642_);
lean_dec(v_a_630_);
lean_dec(v_a_618_);
lean_dec(v_a_606_);
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_a_690_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_694_, 0, v_a_606_);
lean_ctor_set(v___x_694_, 1, v_a_618_);
lean_ctor_set(v___x_694_, 2, v_a_630_);
lean_ctor_set(v___x_694_, 3, v_a_642_);
lean_ctor_set(v___x_694_, 4, v_a_654_);
lean_ctor_set(v___x_694_, 5, v_a_666_);
lean_ctor_set(v___x_694_, 6, v_a_678_);
lean_ctor_set(v___x_694_, 7, v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
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
lean_object* v___x_700_; 
lean_dec(v_x_581_);
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
lean_object* v_elems_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_979_; 
v_elems_860_ = lean_ctor_get(v_v_859_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v_v_859_);
if (v_isSharedCheck_979_ == 0)
{
v___x_862_ = v_v_859_;
v_isShared_863_ = v_isSharedCheck_979_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_elems_860_);
lean_dec(v_v_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_979_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = lean_array_get_size(v_elems_860_);
v___x_865_ = lean_unsigned_to_nat(8u);
v___x_866_ = lean_nat_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_868_ = l_Nat_reprFast(v___x_864_);
v___x_869_ = lean_string_append(v___x_867_, v___x_868_);
lean_dec_ref(v___x_868_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 0);
lean_ctor_set(v___x_862_, 0, v___x_869_);
v___x_871_ = v___x_862_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_del_object(v___x_862_);
v___x_873_ = lean_box(0);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_874_);
lean_inc(v___x_875_);
v___x_876_ = l_Lean_Json_getNat_x3f(v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_a_885_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_876_, 1);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_886_);
lean_inc(v___x_887_);
v___x_888_ = l_Lean_Json_getNat_x3f(v___x_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_897_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_888_, 1);
v___x_898_ = lean_unsigned_to_nat(2u);
v___x_899_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_898_);
lean_inc(v___x_899_);
v___x_900_ = l_Lean_Json_getNat_x3f(v___x_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_a_909_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_900_, 1);
v___x_910_ = lean_unsigned_to_nat(3u);
v___x_911_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_910_);
lean_inc(v___x_911_);
v___x_912_ = l_Lean_Json_getNat_x3f(v___x_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_909_);
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_a_921_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_912_, 1);
v___x_922_ = lean_unsigned_to_nat(4u);
v___x_923_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_922_);
lean_inc(v___x_923_);
v___x_924_ = l_Lean_Json_getNat_x3f(v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_a_921_);
lean_dec(v_a_909_);
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_a_933_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_924_, 1);
v___x_934_ = lean_unsigned_to_nat(5u);
v___x_935_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_934_);
lean_inc(v___x_935_);
v___x_936_ = l_Lean_Json_getNat_x3f(v___x_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_a_933_);
lean_dec(v_a_921_);
lean_dec(v_a_909_);
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_a_945_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_936_, 1);
v___x_946_ = lean_unsigned_to_nat(6u);
v___x_947_ = lean_array_get_borrowed(v___x_873_, v_elems_860_, v___x_946_);
lean_inc(v___x_947_);
v___x_948_ = l_Lean_Json_getNat_x3f(v___x_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_945_);
lean_dec(v_a_933_);
lean_dec(v_a_921_);
lean_dec(v_a_909_);
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_elems_860_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_948_, 1);
v___x_958_ = lean_unsigned_to_nat(7u);
v___x_959_ = lean_array_get(v___x_873_, v_elems_860_, v___x_958_);
lean_dec_ref(v_elems_860_);
v___x_960_ = l_Lean_Json_getNat_x3f(v___x_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_a_957_);
lean_dec(v_a_945_);
lean_dec(v_a_933_);
lean_dec(v_a_921_);
lean_dec(v_a_909_);
lean_dec(v_a_897_);
lean_dec(v_a_885_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_a_969_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v___x_960_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_960_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_973_, 0, v_a_885_);
lean_ctor_set(v___x_973_, 1, v_a_897_);
lean_ctor_set(v___x_973_, 2, v_a_909_);
lean_ctor_set(v___x_973_, 3, v_a_921_);
lean_ctor_set(v___x_973_, 4, v_a_933_);
lean_ctor_set(v___x_973_, 5, v_a_945_);
lean_ctor_set(v___x_973_, 6, v_a_957_);
lean_ctor_set(v___x_973_, 7, v_a_969_);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_856_, v_k_858_, v___x_973_, v_m_857_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
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
lean_object* v___x_980_; 
lean_dec(v_v_859_);
lean_dec_ref(v_k_858_);
lean_dec(v_m_857_);
lean_dec_ref(v___x_856_);
v___x_980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___x_984_, lean_object* v_j_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Json_getObj_x3f(v_j_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___x_984_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_995_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_986_, 1);
v___f_996_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1));
v___x_997_ = lean_box(1);
v___x_998_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_984_, v___f_996_, v___x_997_, v_a_995_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1026_, lean_object* v_parentDecl_x3f_1027_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1027_) == 0)
{
lean_object* v_start_1028_; lean_object* v_end_1029_; lean_object* v_line_1030_; lean_object* v_character_1031_; lean_object* v_line_1032_; lean_object* v_character_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_start_1028_ = lean_ctor_get(v_range_1026_, 0);
v_end_1029_ = lean_ctor_get(v_range_1026_, 1);
v_line_1030_ = lean_ctor_get(v_start_1028_, 0);
v_character_1031_ = lean_ctor_get(v_start_1028_, 1);
v_line_1032_ = lean_ctor_get(v_end_1029_, 0);
v_character_1033_ = lean_ctor_get(v_end_1029_, 1);
v___x_1034_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1033_);
lean_inc(v_line_1032_);
lean_inc(v_character_1031_);
lean_inc(v_line_1030_);
v___x_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1035_, 0, v_line_1030_);
lean_ctor_set(v___x_1035_, 1, v_character_1031_);
lean_ctor_set(v___x_1035_, 2, v_line_1032_);
lean_ctor_set(v___x_1035_, 3, v_character_1033_);
lean_ctor_set(v___x_1035_, 4, v___x_1034_);
return v___x_1035_;
}
else
{
lean_object* v_start_1036_; lean_object* v_end_1037_; lean_object* v_line_1038_; lean_object* v_character_1039_; lean_object* v_line_1040_; lean_object* v_character_1041_; lean_object* v_val_1042_; lean_object* v___x_1043_; 
v_start_1036_ = lean_ctor_get(v_range_1026_, 0);
v_end_1037_ = lean_ctor_get(v_range_1026_, 1);
v_line_1038_ = lean_ctor_get(v_start_1036_, 0);
v_character_1039_ = lean_ctor_get(v_start_1036_, 1);
v_line_1040_ = lean_ctor_get(v_end_1037_, 0);
v_character_1041_ = lean_ctor_get(v_end_1037_, 1);
v_val_1042_ = lean_ctor_get(v_parentDecl_x3f_1027_, 0);
lean_inc(v_val_1042_);
lean_inc(v_character_1041_);
lean_inc(v_line_1040_);
lean_inc(v_character_1039_);
lean_inc(v_line_1038_);
v___x_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1043_, 0, v_line_1038_);
lean_ctor_set(v___x_1043_, 1, v_character_1039_);
lean_ctor_set(v___x_1043_, 2, v_line_1040_);
lean_ctor_set(v___x_1043_, 3, v_character_1041_);
lean_ctor_set(v___x_1043_, 4, v_val_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1044_, lean_object* v_parentDecl_x3f_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1044_, v_parentDecl_x3f_1045_);
lean_dec(v_parentDecl_x3f_1045_);
lean_dec_ref(v_range_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1047_){
_start:
{
lean_object* v_startPosLine_1048_; lean_object* v_startPosCharacter_1049_; lean_object* v_endPosLine_1050_; lean_object* v_endPosCharacter_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_startPosLine_1048_ = lean_ctor_get(v_l_1047_, 0);
v_startPosCharacter_1049_ = lean_ctor_get(v_l_1047_, 1);
v_endPosLine_1050_ = lean_ctor_get(v_l_1047_, 2);
v_endPosCharacter_1051_ = lean_ctor_get(v_l_1047_, 3);
lean_inc(v_startPosCharacter_1049_);
lean_inc(v_startPosLine_1048_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_startPosLine_1048_);
lean_ctor_set(v___x_1052_, 1, v_startPosCharacter_1049_);
lean_inc(v_endPosCharacter_1051_);
lean_inc(v_endPosLine_1050_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_endPosLine_1050_);
lean_ctor_set(v___x_1053_, 1, v_endPosCharacter_1051_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1055_);
lean_dec_ref(v_l_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1057_){
_start:
{
lean_object* v_parentDecl_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_parentDecl_1058_ = lean_ctor_get(v_l_1057_, 4);
v___x_1059_ = lean_string_utf8_byte_size(v_parentDecl_1058_);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_inc_ref(v_parentDecl_1058_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_parentDecl_1058_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_box(0);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1064_);
lean_dec_ref(v_l_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = l_Lean_JsonNumber_fromNat(v_n_1066_);
v___x_1068_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1069_, lean_object* v_l_1070_){
_start:
{
lean_object* v_startPosLine_1071_; lean_object* v_startPosCharacter_1072_; lean_object* v_endPosLine_1073_; lean_object* v_endPosCharacter_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_range_1080_; lean_object* v___x_1081_; 
v_startPosLine_1071_ = lean_ctor_get(v_l_1070_, 0);
v_startPosCharacter_1072_ = lean_ctor_get(v_l_1070_, 1);
v_endPosLine_1073_ = lean_ctor_get(v_l_1070_, 2);
v_endPosCharacter_1074_ = lean_ctor_get(v_l_1070_, 3);
v___x_1075_ = lean_box(0);
lean_inc(v_endPosCharacter_1074_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_endPosCharacter_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
lean_inc(v_endPosLine_1073_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_endPosLine_1073_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_inc(v_startPosCharacter_1072_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_startPosCharacter_1072_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
lean_inc(v_startPosLine_1071_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_startPosLine_1071_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v_range_1080_ = l_List_mapTR_loop___redArg(v___f_1069_, v___x_1079_, v___x_1075_);
v___x_1081_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1070_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = l_List_appendTR___redArg(v_range_1080_, v___x_1075_);
return v___x_1082_;
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1092_; 
v_val_1083_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1085_ = v___x_1081_;
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_val_1083_);
v___x_1088_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v___x_1075_);
v___x_1090_ = l_List_appendTR___redArg(v_range_1080_, v___x_1089_);
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1093_, lean_object* v_l_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1093_, v_l_1094_);
lean_dec_ref(v_l_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_apply_1(v_locationToList_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1101_, lean_object* v___f_1102_, lean_object* v_locationToList_1103_, lean_object* v_i_1104_){
_start:
{
lean_object* v_definition_x3f_1105_; lean_object* v_usages_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1138_; 
v_definition_x3f_1105_ = lean_ctor_get(v_i_1104_, 0);
v_usages_1106_ = lean_ctor_get(v_i_1104_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_i_1104_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1108_ = v_i_1104_;
v_isShared_1109_ = v_isSharedCheck_1138_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_usages_1106_);
lean_inc(v_definition_x3f_1105_);
lean_dec(v_i_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1138_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___y_1112_; 
v___x_1110_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1105_) == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_locationToList_1103_);
v___x_1128_ = lean_box(0);
v___y_1112_ = v___x_1128_;
goto v___jp_1111_;
}
else
{
lean_object* v_val_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_val_1129_ = lean_ctor_get(v_definition_x3f_1105_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_definition_x3f_1105_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v_definition_x3f_1105_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_val_1129_);
lean_dec(v_definition_x3f_1105_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_apply_1(v_locationToList_1103_, v_val_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
v___y_1112_ = v___x_1135_;
goto v___jp_1111_;
}
}
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_inc_ref(v___x_1101_);
v___x_1113_ = l_Lean_Option_toJson___redArg(v___x_1101_, v___y_1112_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v___x_1113_);
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1115_ = v___x_1108_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; size_t v_sz_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1117_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1118_ = lean_array_size(v_usages_1106_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1117_, v___f_1102_, v_sz_1118_, v___x_1119_, v_usages_1106_);
v___x_1121_ = l_Lean_Array_toJson___redArg(v___x_1101_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1116_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_box(0);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1115_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_Json_mkObj(v___x_1125_);
lean_dec_ref_known(v___x_1125_, 2);
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1235_; 
v___x_1154_ = lean_array_get_size(v_a_1153_);
v___x_1155_ = lean_unsigned_to_nat(4u);
v___x_1235_ = lean_nat_dec_eq(v___x_1154_, v___x_1155_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(5u);
v___x_1237_ = lean_nat_dec_eq(v___x_1154_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1238_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1239_ = l_Nat_reprFast(v___x_1154_);
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
else
{
goto v___jp_1156_;
}
}
else
{
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_array_fget_borrowed(v_a_1153_, v___x_1157_);
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
v___x_1170_ = lean_array_fget_borrowed(v_a_1153_, v___x_1169_);
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
v___x_1182_ = lean_array_fget_borrowed(v_a_1153_, v___x_1181_);
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
v___x_1194_ = lean_array_fget_borrowed(v_a_1153_, v___x_1193_);
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
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1234_; 
v_a_1204_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1206_ = v___x_1195_;
v_isShared_1207_ = v_isSharedCheck_1234_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1195_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1234_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_unsigned_to_nat(5u);
v___x_1209_ = lean_nat_dec_eq(v___x_1154_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1210_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1211_, 0, v_a_1168_);
lean_ctor_set(v___x_1211_, 1, v_a_1180_);
lean_ctor_set(v___x_1211_, 2, v_a_1192_);
lean_ctor_set(v___x_1211_, 3, v_a_1204_);
lean_ctor_set(v___x_1211_, 4, v___x_1210_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1211_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_del_object(v___x_1206_);
v___x_1215_ = lean_array_fget_borrowed(v_a_1153_, v___x_1155_);
lean_inc(v___x_1215_);
v___x_1216_ = l_Lean_Json_getStr_x3f(v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1204_);
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
lean_ctor_set(v___x_1229_, 3, v_a_1204_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1242_);
lean_dec_ref(v_a_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v_toLocation_1247_, lean_object* v_j_1248_){
_start:
{
lean_object* v_definition_x3f_1250_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1248_);
v___x_1283_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1244_, v___x_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_j_1248_);
lean_dec_ref(v_toLocation_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___x_1245_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1292_; 
v_a_1292_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1283_, 1);
if (lean_obj_tag(v_a_1292_) == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_box(0);
v_definition_x3f_1250_ = v___x_1293_;
goto v___jp_1249_;
}
else
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1311_; 
v_val_1294_ = lean_ctor_get(v_a_1292_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1296_ = v_a_1292_;
v_isShared_1297_ = v_isSharedCheck_1311_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v_a_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1311_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; 
lean_inc_ref(v_toLocation_1247_);
v___x_1298_ = lean_apply_1(v_toLocation_1247_, v_val_1294_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_del_object(v___x_1296_);
lean_dec(v_j_1248_);
lean_dec_ref(v_toLocation_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___x_1245_);
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
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1298_, 1);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_a_1307_);
v___x_1309_ = v___x_1296_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v_definition_x3f_1250_ = v___x_1309_;
goto v___jp_1249_;
}
}
}
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1252_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1245_, v___x_1251_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_definition_x3f_1250_);
lean_dec_ref(v_toLocation_1247_);
lean_dec_ref(v___x_1246_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v_a_1261_; size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_a_1261_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1252_, 1);
v_sz_1262_ = lean_array_size(v_a_1261_);
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1246_, v_toLocation_1247_, v_sz_1262_, v___x_1263_, v_a_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_definition_x3f_1250_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
v_a_1273_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v___x_1264_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1264_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_definition_x3f_1250_);
lean_ctor_set(v___x_1277_, 1, v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
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
lean_object* v___x_1326_; 
v___x_1326_ = lean_box(1);
return v___x_1326_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(1);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1328_, lean_object* v_a_1329_, lean_object* v_b_1330_, lean_object* v_c_1331_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_a_1329_);
lean_ctor_set(v___x_1332_, 1, v_b_1330_);
v___x_1333_ = lean_apply_2(v_f_1328_, v___x_1332_, v_c_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1334_, lean_object* v_____do__lift_1335_){
_start:
{
lean_object* v_a_1336_; lean_object* v___x_1337_; 
v_a_1336_ = lean_ctor_get(v_____do__lift_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v_____do__lift_1335_);
v___x_1337_ = lean_apply_2(v_toPure_1334_, lean_box(0), v_a_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_map_1340_, lean_object* v_init_1341_, lean_object* v_f_1342_){
_start:
{
lean_object* v_toApplicative_1343_; lean_object* v_toBind_1344_; lean_object* v_toPure_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___f_1348_; lean_object* v___x_1349_; 
v_toApplicative_1343_ = lean_ctor_get(v_inst_1338_, 0);
v_toBind_1344_ = lean_ctor_get(v_inst_1338_, 1);
lean_inc(v_toBind_1344_);
v_toPure_1345_ = lean_ctor_get(v_toApplicative_1343_, 1);
lean_inc(v_toPure_1345_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1346_, 0, v_f_1342_);
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1338_, v___f_1346_, v_init_1341_, v_map_1340_);
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1348_, 0, v_toPure_1345_);
v___x_1349_ = lean_apply_4(v_toBind_1344_, lean_box(0), lean_box(0), v___x_1347_, v___f_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1350_){
_start:
{
lean_object* v___f_1351_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1351_, 0, v_inst_1350_);
return v___f_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1352_, lean_object* v_inst_1353_){
_start:
{
lean_object* v___f_1354_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1354_, 0, v_inst_1353_);
return v___f_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_startPosLine_1357_; lean_object* v_startPosCharacter_1358_; lean_object* v_endPosLine_1359_; lean_object* v_endPosCharacter_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_range_1366_; lean_object* v___x_1367_; 
v_startPosLine_1357_ = lean_ctor_get(v_x_1356_, 0);
v_startPosCharacter_1358_ = lean_ctor_get(v_x_1356_, 1);
v_endPosLine_1359_ = lean_ctor_get(v_x_1356_, 2);
v_endPosCharacter_1360_ = lean_ctor_get(v_x_1356_, 3);
v___x_1361_ = lean_box(0);
lean_inc(v_endPosCharacter_1360_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_endPosCharacter_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc(v_endPosLine_1359_);
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_endPosLine_1359_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
lean_inc(v_startPosCharacter_1358_);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_startPosCharacter_1358_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
lean_inc(v_startPosLine_1357_);
v___x_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_startPosLine_1357_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v_range_1366_ = l_List_mapTR_loop___redArg(v___f_1355_, v___x_1365_, v___x_1361_);
v___x_1367_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1356_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_List_appendTR___redArg(v_range_1366_, v___x_1361_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1378_; 
v_val_1369_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1371_ = v___x_1367_;
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v___x_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 3);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_val_1369_);
v___x_1374_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1361_);
v___x_1376_ = l_List_appendTR___redArg(v_range_1366_, v___x_1375_);
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1379_, v_x_1380_);
lean_dec_ref(v_x_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1382_, lean_object* v___f_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v_snd_1385_; lean_object* v_fst_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1447_; 
v_snd_1385_ = lean_ctor_get(v_x_1384_, 1);
v_fst_1386_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1388_ = v_x_1384_;
v_isShared_1389_ = v_isSharedCheck_1447_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snd_1385_);
lean_inc(v_fst_1386_);
lean_dec(v_x_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1447_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v_definition_x3f_1390_; lean_object* v_usages_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1446_; 
v_definition_x3f_1390_ = lean_ctor_get(v_snd_1385_, 0);
v_usages_1391_ = lean_ctor_get(v_snd_1385_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_snd_1385_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1393_ = v_snd_1385_;
v_isShared_1394_ = v_isSharedCheck_1446_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_usages_1391_);
lean_inc(v_definition_x3f_1390_);
lean_dec(v_snd_1385_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1446_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; lean_object* v___y_1420_; 
v___x_1395_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1386_);
v___x_1396_ = l_Lean_Json_compress(v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1398_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1390_) == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v___f_1383_);
v___x_1422_ = lean_box(0);
v___y_1400_ = v___x_1422_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1423_; lean_object* v_startPosLine_1424_; lean_object* v_startPosCharacter_1425_; lean_object* v_endPosLine_1426_; lean_object* v_endPosCharacter_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_range_1433_; lean_object* v___x_1434_; 
v_val_1423_ = lean_ctor_get(v_definition_x3f_1390_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_definition_x3f_1390_, 1);
v_startPosLine_1424_ = lean_ctor_get(v_val_1423_, 0);
v_startPosCharacter_1425_ = lean_ctor_get(v_val_1423_, 1);
v_endPosLine_1426_ = lean_ctor_get(v_val_1423_, 2);
v_endPosCharacter_1427_ = lean_ctor_get(v_val_1423_, 3);
v___x_1428_ = lean_box(0);
lean_inc(v_endPosCharacter_1427_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_endPosCharacter_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc(v_endPosLine_1426_);
v___x_1430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_endPosLine_1426_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_inc(v_startPosCharacter_1425_);
v___x_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_startPosCharacter_1425_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_inc(v_startPosLine_1424_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_startPosLine_1424_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v_range_1433_ = l_List_mapTR_loop___redArg(v___f_1383_, v___x_1432_, v___x_1428_);
v___x_1434_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1423_);
lean_dec(v_val_1423_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = l_List_appendTR___redArg(v_range_1433_, v___x_1428_);
v___y_1420_ = v___x_1435_;
goto v___jp_1419_;
}
else
{
lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
v_val_1436_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1438_ = v___x_1434_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_dec(v___x_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 3);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_val_1436_);
v___x_1441_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___x_1428_);
v___x_1443_ = l_List_appendTR___redArg(v_range_1433_, v___x_1442_);
v___y_1420_ = v___x_1443_;
goto v___jp_1419_;
}
}
}
}
v___jp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = l_Lean_Option_toJson___redArg(v___x_1397_, v___y_1400_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v___x_1401_);
lean_ctor_set(v___x_1388_, 0, v___x_1398_);
v___x_1403_ = v___x_1388_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; size_t v_sz_1406_; size_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1404_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1405_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1406_ = lean_array_size(v_usages_1391_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1405_, v___f_1382_, v_sz_1406_, v___x_1407_, v_usages_1391_);
v___x_1409_ = l_Lean_Array_toJson___redArg(v___x_1397_, v___x_1408_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1409_);
lean_ctor_set(v___x_1393_, 0, v___x_1404_);
v___x_1411_ = v___x_1393_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1403_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l_Lean_Json_mkObj(v___x_1414_);
lean_dec_ref_known(v___x_1414_, 2);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1396_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
return v___x_1416_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___y_1420_);
v___y_1400_ = v___x_1421_;
goto v___jp_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1448_, lean_object* v_x2_1449_, lean_object* v_x3_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_x1_1448_);
lean_ctor_set(v___x_1451_, 1, v_x2_1449_);
v___x_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v_x3_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1453_, lean_object* v___f_1454_, lean_object* v_m_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1458_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1457_, v___f_1453_, v___x_1456_, v_m_1455_);
v___x_1459_ = l_List_mapTR_loop___redArg(v___f_1454_, v___x_1458_, v___x_1456_);
v___x_1460_ = l_Lean_Json_mkObj(v___x_1459_);
lean_dec(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1471_, lean_object* v_m_1472_, lean_object* v_k_1473_, lean_object* v_v_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Json_parse(v_k_1473_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1485_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
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
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1494_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1495_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1497_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1474_);
v___x_1498_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1474_, v___x_1496_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1628_; 
v_a_1507_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1509_ = v___x_1498_;
v_isShared_1510_ = v_isSharedCheck_1628_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1498_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1628_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v_definition_x3f_1513_; lean_object* v_a_1548_; 
v___x_1511_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1507_) == 0)
{
lean_object* v___x_1550_; 
lean_del_object(v___x_1509_);
v___x_1550_ = lean_box(0);
v_definition_x3f_1513_ = v___x_1550_;
goto v___jp_1512_;
}
else
{
lean_object* v_val_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1619_; 
v_val_1551_ = lean_ctor_get(v_a_1507_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v_a_1507_, 1);
v___x_1552_ = lean_array_get_size(v_val_1551_);
v___x_1553_ = lean_unsigned_to_nat(4u);
v___x_1619_ = lean_nat_dec_eq(v___x_1552_, v___x_1553_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(5u);
v___x_1621_ = lean_nat_dec_eq(v___x_1552_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
lean_dec(v_val_1551_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v___x_1622_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1623_ = l_Nat_reprFast(v___x_1552_);
v___x_1624_ = lean_string_append(v___x_1622_, v___x_1623_);
lean_dec_ref(v___x_1623_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1624_);
v___x_1626_ = v___x_1509_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
else
{
lean_del_object(v___x_1509_);
goto v___jp_1554_;
}
}
else
{
lean_del_object(v___x_1509_);
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_fget_borrowed(v_val_1551_, v___x_1555_);
lean_inc(v___x_1556_);
v___x_1557_ = l_Lean_Json_getNat_x3f(v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_val_1551_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
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
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_array_fget_borrowed(v_val_1551_, v___x_1567_);
lean_inc(v___x_1568_);
v___x_1569_ = l_Lean_Json_getNat_x3f(v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1566_);
lean_dec(v_val_1551_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
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
v___x_1579_ = lean_unsigned_to_nat(2u);
v___x_1580_ = lean_array_fget_borrowed(v_val_1551_, v___x_1579_);
lean_inc(v___x_1580_);
v___x_1581_ = l_Lean_Json_getNat_x3f(v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1578_);
lean_dec(v_a_1566_);
lean_dec(v_val_1551_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
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
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1590_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1591_ = lean_unsigned_to_nat(3u);
v___x_1592_ = lean_array_fget_borrowed(v_val_1551_, v___x_1591_);
lean_inc(v___x_1592_);
v___x_1593_ = l_Lean_Json_getNat_x3f(v___x_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v_a_1566_);
lean_dec(v_val_1551_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1603_ = lean_unsigned_to_nat(5u);
v___x_1604_ = lean_nat_dec_eq(v___x_1552_, v___x_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_val_1551_);
v___x_1605_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1566_);
lean_ctor_set(v___x_1606_, 1, v_a_1578_);
lean_ctor_set(v___x_1606_, 2, v_a_1590_);
lean_ctor_set(v___x_1606_, 3, v_a_1602_);
lean_ctor_set(v___x_1606_, 4, v___x_1605_);
v_a_1548_ = v___x_1606_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_array_fget(v_val_1551_, v___x_1553_);
lean_dec(v_val_1551_);
v___x_1608_ = l_Lean_Json_getStr_x3f(v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1602_);
lean_dec(v_a_1590_);
lean_dec(v_a_1578_);
lean_dec(v_a_1566_);
lean_dec(v_a_1494_);
lean_dec(v_v_1474_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1618_, 0, v_a_1566_);
lean_ctor_set(v___x_1618_, 1, v_a_1578_);
lean_ctor_set(v___x_1618_, 2, v_a_1590_);
lean_ctor_set(v___x_1618_, 3, v_a_1602_);
lean_ctor_set(v___x_1618_, 4, v_a_1617_);
v_a_1548_ = v___x_1618_;
goto v___jp_1547_;
}
}
}
}
}
}
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1515_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1474_, v___x_1511_, v___x_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v_definition_x3f_1513_);
lean_dec(v_a_1494_);
lean_dec(v_m_1472_);
lean_dec_ref(v_toLocation_1471_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_object* v_a_1524_; size_t v_sz_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v_a_1524_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1515_, 1);
v_sz_1525_ = lean_array_size(v_a_1524_);
v___x_1526_ = ((size_t)0ULL);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1495_, v_toLocation_1471_, v_sz_1525_, v___x_1526_, v_a_1524_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_definition_x3f_1513_);
lean_dec(v_a_1494_);
lean_dec(v_m_1472_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1546_; 
v_a_1536_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1538_ = v___x_1527_;
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1527_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1546_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_definition_x3f_1513_);
lean_ctor_set(v___x_1540_, 1, v_a_1536_);
v___x_1541_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1541_, v_a_1494_, v___x_1540_, v_m_1472_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1542_);
v___x_1544_ = v___x_1538_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
v___jp_1547_:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_a_1548_);
v_definition_x3f_1513_ = v___x_1549_;
goto v___jp_1512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1629_, lean_object* v___f_1630_, lean_object* v_j_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Json_getObj_x3f(v_j_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v___f_1630_);
lean_dec_ref(v___x_1629_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1632_, 1);
v___x_1642_ = lean_box(1);
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1629_, v___f_1630_, v___x_1642_, v_a_1641_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1650_, lean_object* v_k_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = l_Lean_Json_getObjValD(v_j_1650_, v_k_1651_);
v___x_1653_ = l_Lean_Json_getNat_x3f(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1654_, lean_object* v_k_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1654_, v_k_1655_);
lean_dec_ref(v_k_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1657_, lean_object* v_k_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = l_Lean_Json_getObjValD(v_j_1657_, v_k_1658_);
v___x_1660_ = l_Lean_Json_getBool_x3f(v___x_1659_);
lean_dec(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1661_, lean_object* v_k_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1661_, v_k_1662_);
lean_dec_ref(v_k_1662_);
return v_res_1663_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_bs_1668_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_lt(v_i_1667_, v_sz_1666_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_bs_1668_);
return v___x_1672_;
}
else
{
lean_object* v_v_1673_; 
v_v_1673_ = lean_array_uget_borrowed(v_bs_1668_, v_i_1667_);
if (lean_obj_tag(v_v_1673_) == 4)
{
lean_object* v_elems_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_elems_1674_ = lean_ctor_get(v_v_1673_, 0);
v___x_1675_ = lean_array_get_size(v_elems_1674_);
v___x_1676_ = lean_unsigned_to_nat(4u);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v_bs_1668_);
goto v___jp_1669_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_array_fget_borrowed(v_elems_1674_, v___x_1678_);
lean_inc(v___x_1679_);
v___x_1680_ = l_Lean_Json_getStr_x3f(v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_bs_1668_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_a_1689_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_array_fget_borrowed(v_elems_1674_, v___x_1690_);
v___x_1692_ = l_Lean_Json_getBool_x3f(v___x_1691_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_a_1689_);
lean_dec_ref(v_bs_1668_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_a_1701_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1702_ = lean_unsigned_to_nat(2u);
v___x_1703_ = lean_array_fget_borrowed(v_elems_1674_, v___x_1702_);
v___x_1704_ = l_Lean_Json_getBool_x3f(v___x_1703_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_a_1701_);
lean_dec(v_a_1689_);
lean_dec_ref(v_bs_1668_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1714_ = lean_unsigned_to_nat(3u);
v___x_1715_ = lean_array_fget_borrowed(v_elems_1674_, v___x_1714_);
v___x_1716_ = l_Lean_Json_getBool_x3f(v___x_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1713_);
lean_dec(v_a_1701_);
lean_dec(v_a_1689_);
lean_dec_ref(v_bs_1668_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v_bs_x27_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; uint8_t v___x_1729_; uint8_t v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v_a_1725_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1716_, 1);
v_bs_x27_1726_ = lean_array_uset(v_bs_1668_, v_i_1667_, v___x_1678_);
v___x_1727_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1727_, 0, v_a_1689_);
v___x_1728_ = lean_unbox(v_a_1701_);
lean_dec(v_a_1701_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*1, v___x_1728_);
v___x_1729_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*1 + 1, v___x_1729_);
v___x_1730_ = lean_unbox(v_a_1725_);
lean_dec(v_a_1725_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*1 + 2, v___x_1730_);
v___x_1731_ = ((size_t)1ULL);
v___x_1732_ = lean_usize_add(v_i_1667_, v___x_1731_);
v___x_1733_ = lean_array_uset(v_bs_x27_1726_, v_i_1667_, v___x_1727_);
v_i_1667_ = v___x_1732_;
v_bs_1668_ = v___x_1733_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1668_);
goto v___jp_1669_;
}
}
v___jp_1669_:
{
lean_object* v___x_1670_; 
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1670_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1666_ = stack[0].m_num;
size_t v_i_1667_ = stack[1].m_num;
lean_object* v_bs_1668_ = stack[2].m_obj;
lean_object* v_res_1735_;
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1666_, v_i_1667_, v_bs_1668_);
stack->m_obj
 = v_res_1735_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1889_, size_t v_i_1890_, lean_object* v_bs_1891_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1889_ = stack[0].m_num;
size_t v_i_1890_ = stack[1].m_num;
lean_object* v_bs_1891_ = stack[2].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1889_, v_i_1890_, v_bs_1891_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_bs_1918_){
_start:
{
size_t v_sz_boxed_1919_; size_t v_i_boxed_1920_; lean_object* v_res_1921_; 
v_sz_boxed_1919_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1920_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1919_, v_i_boxed_1920_, v_bs_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1922_){
_start:
{
size_t v_sz_1923_; size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_sz_1923_ = lean_array_size(v_a_1922_);
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1923_, v___x_1924_, v_a_1922_);
v___x_1926_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
if (lean_obj_tag(v_a_1927_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_array_to_list(v_a_1928_);
return v___x_1929_;
}
else
{
lean_object* v_head_1930_; lean_object* v_tail_1931_; lean_object* v___x_1932_; 
v_head_1930_ = lean_ctor_get(v_a_1927_, 0);
lean_inc(v_head_1930_);
v_tail_1931_ = lean_ctor_get(v_a_1927_, 1);
lean_inc(v_tail_1931_);
lean_dec_ref_known(v_a_1927_, 2);
v___x_1932_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1928_, v_head_1930_);
v_a_1927_ = v_tail_1931_;
v_a_1928_ = v___x_1932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1936_){
_start:
{
lean_object* v_version_1937_; uint8_t v_isSetupFailure_1938_; lean_object* v_directImports_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_version_1937_ = lean_ctor_get(v_x_1936_, 0);
lean_inc(v_version_1937_);
v_isSetupFailure_1938_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*2);
v_directImports_1939_ = lean_ctor_get(v_x_1936_, 1);
lean_inc_ref(v_directImports_1939_);
lean_dec_ref(v_x_1936_);
v___x_1940_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1941_ = l_Lean_JsonNumber_fromNat(v_version_1937_);
v___x_1942_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1940_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1947_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1947_, 0, v_isSetupFailure_1938_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1944_);
v___x_1950_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1951_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1939_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v___x_1944_);
v___x_1954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1944_);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1949_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1945_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1958_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1956_, v___x_1957_);
v___x_1959_ = l_Lean_Json_mkObj(v___x_1958_);
lean_dec(v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1962_, lean_object* v_v_1963_, lean_object* v_t_1964_){
_start:
{
if (lean_obj_tag(v_t_1964_) == 0)
{
lean_object* v_size_1965_; lean_object* v_k_1966_; lean_object* v_v_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2249_; 
v_size_1965_ = lean_ctor_get(v_t_1964_, 0);
v_k_1966_ = lean_ctor_get(v_t_1964_, 1);
v_v_1967_ = lean_ctor_get(v_t_1964_, 2);
v_l_1968_ = lean_ctor_get(v_t_1964_, 3);
v_r_1969_ = lean_ctor_get(v_t_1964_, 4);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_t_1964_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_1971_ = v_t_1964_;
v_isShared_1972_ = v_isSharedCheck_2249_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_r_1969_);
lean_inc(v_l_1968_);
lean_inc(v_v_1967_);
lean_inc(v_k_1966_);
lean_inc(v_size_1965_);
lean_dec(v_t_1964_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2249_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_string_compare(v_k_1962_, v_k_1966_);
switch(v___x_1973_)
{
case 0:
{
lean_object* v_impl_1974_; lean_object* v___x_1975_; 
lean_dec(v_size_1965_);
v_impl_1974_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1962_, v_v_1963_, v_l_1968_);
v___x_1975_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1969_) == 0)
{
lean_object* v_size_1976_; lean_object* v_size_1977_; lean_object* v_k_1978_; lean_object* v_v_1979_; lean_object* v_l_1980_; lean_object* v_r_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_size_1976_ = lean_ctor_get(v_r_1969_, 0);
v_size_1977_ = lean_ctor_get(v_impl_1974_, 0);
v_k_1978_ = lean_ctor_get(v_impl_1974_, 1);
v_v_1979_ = lean_ctor_get(v_impl_1974_, 2);
v_l_1980_ = lean_ctor_get(v_impl_1974_, 3);
v_r_1981_ = lean_ctor_get(v_impl_1974_, 4);
lean_inc(v_r_1981_);
v___x_1982_ = lean_unsigned_to_nat(3u);
v___x_1983_ = lean_nat_mul(v___x_1982_, v_size_1976_);
v___x_1984_ = lean_nat_dec_lt(v___x_1983_, v_size_1977_);
lean_dec(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
lean_dec(v_r_1981_);
v___x_1985_ = lean_nat_add(v___x_1975_, v_size_1977_);
v___x_1986_ = lean_nat_add(v___x_1985_, v_size_1976_);
lean_dec(v___x_1985_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 3, v_impl_1974_);
lean_ctor_set(v___x_1971_, 0, v___x_1986_);
v___x_1988_ = v___x_1971_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_impl_1974_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_r_1969_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2055_; 
lean_inc(v_l_1980_);
lean_inc(v_v_1979_);
lean_inc(v_k_1978_);
lean_inc(v_size_1977_);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_impl_1974_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; lean_object* v_unused_2057_; lean_object* v_unused_2058_; lean_object* v_unused_2059_; lean_object* v_unused_2060_; 
v_unused_2056_ = lean_ctor_get(v_impl_1974_, 4);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_impl_1974_, 3);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_impl_1974_, 2);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_impl_1974_, 1);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_impl_1974_, 0);
lean_dec(v_unused_2060_);
v___x_1991_ = v_impl_1974_;
v_isShared_1992_ = v_isSharedCheck_2055_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_impl_1974_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2055_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_size_1993_; lean_object* v_size_1994_; lean_object* v_k_1995_; lean_object* v_v_1996_; lean_object* v_l_1997_; lean_object* v_r_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_size_1993_ = lean_ctor_get(v_l_1980_, 0);
v_size_1994_ = lean_ctor_get(v_r_1981_, 0);
v_k_1995_ = lean_ctor_get(v_r_1981_, 1);
v_v_1996_ = lean_ctor_get(v_r_1981_, 2);
v_l_1997_ = lean_ctor_get(v_r_1981_, 3);
v_r_1998_ = lean_ctor_get(v_r_1981_, 4);
v___x_1999_ = lean_unsigned_to_nat(2u);
v___x_2000_ = lean_nat_mul(v___x_1999_, v_size_1993_);
v___x_2001_ = lean_nat_dec_lt(v_size_1994_, v___x_2000_);
lean_dec(v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2030_; 
lean_inc(v_r_1998_);
lean_inc(v_l_1997_);
lean_inc(v_v_1996_);
lean_inc(v_k_1995_);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_r_1981_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; lean_object* v_unused_2035_; 
v_unused_2031_ = lean_ctor_get(v_r_1981_, 4);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1981_, 3);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_1981_, 2);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_r_1981_, 1);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_r_1981_, 0);
lean_dec(v_unused_2035_);
v___x_2003_ = v_r_1981_;
v_isShared_2004_ = v_isSharedCheck_2030_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_r_1981_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2030_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___x_2018_; lean_object* v___y_2020_; 
v___x_2005_ = lean_nat_add(v___x_1975_, v_size_1977_);
lean_dec(v_size_1977_);
v___x_2006_ = lean_nat_add(v___x_2005_, v_size_1976_);
lean_dec(v___x_2005_);
v___x_2018_ = lean_nat_add(v___x_1975_, v_size_1993_);
if (lean_obj_tag(v_l_1997_) == 0)
{
lean_object* v_size_2028_; 
v_size_2028_ = lean_ctor_get(v_l_1997_, 0);
lean_inc(v_size_2028_);
v___y_2020_ = v_size_2028_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_unsigned_to_nat(0u);
v___y_2020_ = v___x_2029_;
goto v___jp_2019_;
}
v___jp_2007_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_nat_add(v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v_r_1969_);
lean_ctor_set(v___x_2003_, 3, v_r_1998_);
lean_ctor_set(v___x_2003_, 2, v_v_1967_);
lean_ctor_set(v___x_2003_, 1, v_k_1966_);
lean_ctor_set(v___x_2003_, 0, v___x_2011_);
v___x_2013_ = v___x_2003_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_r_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_r_1969_);
v___x_2013_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v___x_2013_);
lean_ctor_set(v___x_1991_, 3, v___y_2008_);
lean_ctor_set(v___x_1991_, 2, v_v_1996_);
lean_ctor_set(v___x_1991_, 1, v_k_1995_);
lean_ctor_set(v___x_1991_, 0, v___x_2006_);
v___x_2015_ = v___x_1991_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1995_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1996_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v___y_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
v___jp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_nat_add(v___x_2018_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec(v___x_2018_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_l_1997_);
lean_ctor_set(v___x_1971_, 3, v_l_1980_);
lean_ctor_set(v___x_1971_, 2, v_v_1979_);
lean_ctor_set(v___x_1971_, 1, v_k_1978_);
lean_ctor_set(v___x_1971_, 0, v___x_2021_);
v___x_2023_ = v___x_1971_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_k_1978_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_v_1979_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_l_1980_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v_l_1997_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_nat_add(v___x_1975_, v_size_1976_);
if (lean_obj_tag(v_r_1998_) == 0)
{
lean_object* v_size_2025_; 
v_size_2025_ = lean_ctor_get(v_r_1998_, 0);
lean_inc(v_size_2025_);
v___y_2008_ = v___x_2023_;
v___y_2009_ = v___x_2024_;
v___y_2010_ = v_size_2025_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___y_2008_ = v___x_2023_;
v___y_2009_ = v___x_2024_;
v___y_2010_ = v___x_2026_;
goto v___jp_2007_;
}
}
}
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_del_object(v___x_1971_);
v___x_2036_ = lean_nat_add(v___x_1975_, v_size_1977_);
lean_dec(v_size_1977_);
v___x_2037_ = lean_nat_add(v___x_2036_, v_size_1976_);
lean_dec(v___x_2036_);
v___x_2038_ = lean_nat_add(v___x_1975_, v_size_1976_);
v___x_2039_ = lean_nat_add(v___x_2038_, v_size_1994_);
lean_dec(v___x_2038_);
lean_inc_ref(v_r_1969_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_r_1969_);
lean_ctor_set(v___x_1991_, 3, v_r_1981_);
lean_ctor_set(v___x_1991_, 2, v_v_1967_);
lean_ctor_set(v___x_1991_, 1, v_k_1966_);
lean_ctor_set(v___x_1991_, 0, v___x_2039_);
v___x_2041_ = v___x_1991_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_r_1981_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_r_1969_);
v___x_2041_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_isSharedCheck_2048_ = !lean_is_exclusive(v_r_1969_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2049_ = lean_ctor_get(v_r_1969_, 4);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v_r_1969_, 3);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v_r_1969_, 2);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_r_1969_, 1);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_r_1969_, 0);
lean_dec(v_unused_2053_);
v___x_2043_ = v_r_1969_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_r_1969_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v___x_2041_);
lean_ctor_set(v___x_2043_, 3, v_l_1980_);
lean_ctor_set(v___x_2043_, 2, v_v_1979_);
lean_ctor_set(v___x_2043_, 1, v_k_1978_);
lean_ctor_set(v___x_2043_, 0, v___x_2037_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_k_1978_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_v_1979_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_l_1980_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v___x_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2061_; 
v_l_2061_ = lean_ctor_get(v_impl_1974_, 3);
if (lean_obj_tag(v_l_2061_) == 0)
{
lean_object* v_r_2062_; lean_object* v_k_2063_; lean_object* v_v_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
lean_inc_ref(v_l_2061_);
v_r_2062_ = lean_ctor_get(v_impl_1974_, 4);
v_k_2063_ = lean_ctor_get(v_impl_1974_, 1);
v_v_2064_ = lean_ctor_get(v_impl_1974_, 2);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_impl_1974_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2076_ = lean_ctor_get(v_impl_1974_, 3);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1974_, 0);
lean_dec(v_unused_2077_);
v___x_2066_ = v_impl_1974_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_r_2062_);
lean_inc(v_v_2064_);
lean_inc(v_k_2063_);
lean_dec(v_impl_1974_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2062_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 3, v_r_2062_);
lean_ctor_set(v___x_2066_, 2, v_v_1967_);
lean_ctor_set(v___x_2066_, 1, v_k_1966_);
lean_ctor_set(v___x_2066_, 0, v___x_1975_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_r_2062_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_r_2062_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_2070_);
lean_ctor_set(v___x_1971_, 3, v_l_2061_);
lean_ctor_set(v___x_1971_, 2, v_v_2064_);
lean_ctor_set(v___x_1971_, 1, v_k_2063_);
lean_ctor_set(v___x_1971_, 0, v___x_2068_);
v___x_2072_ = v___x_1971_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_l_2061_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_r_2078_; 
v_r_2078_ = lean_ctor_get(v_impl_1974_, 4);
lean_inc(v_r_2078_);
if (lean_obj_tag(v_r_2078_) == 0)
{
lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2103_; 
lean_inc(v_l_2061_);
v_k_2079_ = lean_ctor_get(v_impl_1974_, 1);
v_v_2080_ = lean_ctor_get(v_impl_1974_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_impl_1974_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2104_ = lean_ctor_get(v_impl_1974_, 4);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_impl_1974_, 3);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_impl_1974_, 0);
lean_dec(v_unused_2106_);
v___x_2082_ = v_impl_1974_;
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
lean_dec(v_impl_1974_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2099_; 
v_k_2084_ = lean_ctor_get(v_r_2078_, 1);
v_v_2085_ = lean_ctor_get(v_r_2078_, 2);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_r_2078_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; lean_object* v_unused_2101_; lean_object* v_unused_2102_; 
v_unused_2100_ = lean_ctor_get(v_r_2078_, 4);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_r_2078_, 3);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_r_2078_, 0);
lean_dec(v_unused_2102_);
v___x_2087_ = v_r_2078_;
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_r_2078_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_unsigned_to_nat(3u);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 4, v_l_2061_);
lean_ctor_set(v___x_2087_, 3, v_l_2061_);
lean_ctor_set(v___x_2087_, 2, v_v_2080_);
lean_ctor_set(v___x_2087_, 1, v_k_2079_);
lean_ctor_set(v___x_2087_, 0, v___x_1975_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_l_2061_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_l_2061_);
v___x_2091_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v_l_2061_);
lean_ctor_set(v___x_2082_, 2, v_v_1967_);
lean_ctor_set(v___x_2082_, 1, v_k_1966_);
lean_ctor_set(v___x_2082_, 0, v___x_1975_);
v___x_2093_ = v___x_2082_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_l_2061_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_l_2061_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_2093_);
lean_ctor_set(v___x_1971_, 3, v___x_2091_);
lean_ctor_set(v___x_1971_, 2, v_v_2085_);
lean_ctor_set(v___x_1971_, 1, v_k_2084_);
lean_ctor_set(v___x_1971_, 0, v___x_2089_);
v___x_2095_ = v___x_1971_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_unsigned_to_nat(2u);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_r_2078_);
lean_ctor_set(v___x_1971_, 3, v_impl_1974_);
lean_ctor_set(v___x_1971_, 0, v___x_2107_);
v___x_2109_ = v___x_1971_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_impl_1974_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_r_2078_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2112_; 
lean_dec(v_v_1967_);
lean_dec(v_k_1966_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 2, v_v_1963_);
lean_ctor_set(v___x_1971_, 1, v_k_1962_);
v___x_2112_ = v___x_1971_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_size_1965_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_1962_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_1963_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_r_1969_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
default: 
{
lean_object* v_impl_2114_; lean_object* v___x_2115_; 
lean_dec(v_size_1965_);
v_impl_2114_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1962_, v_v_1963_, v_r_1969_);
v___x_2115_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1968_) == 0)
{
lean_object* v_size_2116_; lean_object* v_size_2117_; lean_object* v_k_2118_; lean_object* v_v_2119_; lean_object* v_l_2120_; lean_object* v_r_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_size_2116_ = lean_ctor_get(v_l_1968_, 0);
v_size_2117_ = lean_ctor_get(v_impl_2114_, 0);
v_k_2118_ = lean_ctor_get(v_impl_2114_, 1);
v_v_2119_ = lean_ctor_get(v_impl_2114_, 2);
v_l_2120_ = lean_ctor_get(v_impl_2114_, 3);
lean_inc(v_l_2120_);
v_r_2121_ = lean_ctor_get(v_impl_2114_, 4);
v___x_2122_ = lean_unsigned_to_nat(3u);
v___x_2123_ = lean_nat_mul(v___x_2122_, v_size_2116_);
v___x_2124_ = lean_nat_dec_lt(v___x_2123_, v_size_2117_);
lean_dec(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
lean_dec(v_l_2120_);
v___x_2125_ = lean_nat_add(v___x_2115_, v_size_2116_);
v___x_2126_ = lean_nat_add(v___x_2125_, v_size_2117_);
lean_dec(v___x_2125_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_impl_2114_);
lean_ctor_set(v___x_1971_, 0, v___x_2126_);
v___x_2128_ = v___x_1971_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_impl_2114_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
else
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2193_; 
lean_inc(v_r_2121_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
lean_inc(v_size_2117_);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_impl_2114_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; 
v_unused_2194_ = lean_ctor_get(v_impl_2114_, 4);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_impl_2114_, 3);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_impl_2114_, 2);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_impl_2114_, 1);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_impl_2114_, 0);
lean_dec(v_unused_2198_);
v___x_2131_ = v_impl_2114_;
v_isShared_2132_ = v_isSharedCheck_2193_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v_impl_2114_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2193_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_size_2133_; lean_object* v_k_2134_; lean_object* v_v_2135_; lean_object* v_l_2136_; lean_object* v_r_2137_; lean_object* v_size_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_size_2133_ = lean_ctor_get(v_l_2120_, 0);
v_k_2134_ = lean_ctor_get(v_l_2120_, 1);
v_v_2135_ = lean_ctor_get(v_l_2120_, 2);
v_l_2136_ = lean_ctor_get(v_l_2120_, 3);
v_r_2137_ = lean_ctor_get(v_l_2120_, 4);
v_size_2138_ = lean_ctor_get(v_r_2121_, 0);
v___x_2139_ = lean_unsigned_to_nat(2u);
v___x_2140_ = lean_nat_mul(v___x_2139_, v_size_2138_);
v___x_2141_ = lean_nat_dec_lt(v_size_2133_, v___x_2140_);
lean_dec(v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2169_; 
lean_inc(v_r_2137_);
lean_inc(v_l_2136_);
lean_inc(v_v_2135_);
lean_inc(v_k_2134_);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_l_2120_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2170_ = lean_ctor_get(v_l_2120_, 4);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_l_2120_, 3);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_l_2120_, 2);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_l_2120_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_l_2120_, 0);
lean_dec(v_unused_2174_);
v___x_2143_ = v_l_2120_;
v_isShared_2144_ = v_isSharedCheck_2169_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v_l_2120_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2169_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2159_; 
v___x_2145_ = lean_nat_add(v___x_2115_, v_size_2116_);
v___x_2146_ = lean_nat_add(v___x_2145_, v_size_2117_);
lean_dec(v_size_2117_);
if (lean_obj_tag(v_l_2136_) == 0)
{
lean_object* v_size_2167_; 
v_size_2167_ = lean_ctor_get(v_l_2136_, 0);
lean_inc(v_size_2167_);
v___y_2159_ = v_size_2167_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_unsigned_to_nat(0u);
v___y_2159_ = v___x_2168_;
goto v___jp_2158_;
}
v___jp_2147_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_nat_add(v___y_2148_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec(v___y_2148_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v_r_2121_);
lean_ctor_set(v___x_2143_, 3, v_r_2137_);
lean_ctor_set(v___x_2143_, 2, v_v_2119_);
lean_ctor_set(v___x_2143_, 1, v_k_2118_);
lean_ctor_set(v___x_2143_, 0, v___x_2151_);
v___x_2153_ = v___x_2143_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_r_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_r_2121_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 4, v___x_2153_);
lean_ctor_set(v___x_2131_, 3, v___y_2149_);
lean_ctor_set(v___x_2131_, 2, v_v_2135_);
lean_ctor_set(v___x_2131_, 1, v_k_2134_);
lean_ctor_set(v___x_2131_, 0, v___x_2146_);
v___x_2155_ = v___x_2131_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2134_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2135_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v___y_2149_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
v___jp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_nat_add(v___x_2145_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec(v___x_2145_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_l_2136_);
lean_ctor_set(v___x_1971_, 0, v___x_2160_);
v___x_2162_ = v___x_1971_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_l_2136_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_nat_add(v___x_2115_, v_size_2138_);
if (lean_obj_tag(v_r_2137_) == 0)
{
lean_object* v_size_2164_; 
v_size_2164_ = lean_ctor_get(v_r_2137_, 0);
lean_inc(v_size_2164_);
v___y_2148_ = v___x_2163_;
v___y_2149_ = v___x_2162_;
v___y_2150_ = v_size_2164_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___y_2148_ = v___x_2163_;
v___y_2149_ = v___x_2162_;
v___y_2150_ = v___x_2165_;
goto v___jp_2147_;
}
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
lean_del_object(v___x_1971_);
v___x_2175_ = lean_nat_add(v___x_2115_, v_size_2116_);
v___x_2176_ = lean_nat_add(v___x_2175_, v_size_2117_);
lean_dec(v_size_2117_);
v___x_2177_ = lean_nat_add(v___x_2175_, v_size_2133_);
lean_dec(v___x_2175_);
lean_inc_ref(v_l_1968_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 4, v_l_2120_);
lean_ctor_set(v___x_2131_, 3, v_l_1968_);
lean_ctor_set(v___x_2131_, 2, v_v_1967_);
lean_ctor_set(v___x_2131_, 1, v_k_1966_);
lean_ctor_set(v___x_2131_, 0, v___x_2177_);
v___x_2179_ = v___x_2131_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_l_2120_);
v___x_2179_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_isSharedCheck_2186_ = !lean_is_exclusive(v_l_1968_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2187_ = lean_ctor_get(v_l_1968_, 4);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_l_1968_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_l_1968_, 2);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_1968_, 1);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_l_1968_, 0);
lean_dec(v_unused_2191_);
v___x_2181_ = v_l_1968_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v_l_1968_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 4, v_r_2121_);
lean_ctor_set(v___x_2181_, 3, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v_v_2119_);
lean_ctor_set(v___x_2181_, 1, v_k_2118_);
lean_ctor_set(v___x_2181_, 0, v___x_2176_);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_r_2121_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2199_; 
v_l_2199_ = lean_ctor_get(v_impl_2114_, 3);
lean_inc(v_l_2199_);
if (lean_obj_tag(v_l_2199_) == 0)
{
lean_object* v_r_2200_; lean_object* v_k_2201_; lean_object* v_v_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2225_; 
v_r_2200_ = lean_ctor_get(v_impl_2114_, 4);
v_k_2201_ = lean_ctor_get(v_impl_2114_, 1);
v_v_2202_ = lean_ctor_get(v_impl_2114_, 2);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_impl_2114_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2226_ = lean_ctor_get(v_impl_2114_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_impl_2114_, 0);
lean_dec(v_unused_2227_);
v___x_2204_ = v_impl_2114_;
v_isShared_2205_ = v_isSharedCheck_2225_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_r_2200_);
lean_inc(v_v_2202_);
lean_inc(v_k_2201_);
lean_dec(v_impl_2114_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2225_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2221_; 
v_k_2206_ = lean_ctor_get(v_l_2199_, 1);
v_v_2207_ = lean_ctor_get(v_l_2199_, 2);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_l_2199_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; lean_object* v_unused_2223_; lean_object* v_unused_2224_; 
v_unused_2222_ = lean_ctor_get(v_l_2199_, 4);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_l_2199_, 3);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_l_2199_, 0);
lean_dec(v_unused_2224_);
v___x_2209_ = v_l_2199_;
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_v_2207_);
lean_inc(v_k_2206_);
lean_dec(v_l_2199_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2200_, 2);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 4, v_r_2200_);
lean_ctor_set(v___x_2209_, 3, v_r_2200_);
lean_ctor_set(v___x_2209_, 2, v_v_1967_);
lean_ctor_set(v___x_2209_, 1, v_k_1966_);
lean_ctor_set(v___x_2209_, 0, v___x_2115_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_r_2200_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v_r_2200_);
v___x_2213_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
lean_inc(v_r_2200_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 3, v_r_2200_);
lean_ctor_set(v___x_2204_, 0, v___x_2115_);
v___x_2215_ = v___x_2204_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_2201_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2202_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_r_2200_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_r_2200_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_2215_);
lean_ctor_set(v___x_1971_, 3, v___x_2213_);
lean_ctor_set(v___x_1971_, 2, v_v_2207_);
lean_ctor_set(v___x_1971_, 1, v_k_2206_);
lean_ctor_set(v___x_1971_, 0, v___x_2211_);
v___x_2217_ = v___x_1971_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
else
{
lean_object* v_r_2228_; 
v_r_2228_ = lean_ctor_get(v_impl_2114_, 4);
lean_inc(v_r_2228_);
if (lean_obj_tag(v_r_2228_) == 0)
{
lean_object* v_k_2229_; lean_object* v_v_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2241_; 
v_k_2229_ = lean_ctor_get(v_impl_2114_, 1);
v_v_2230_ = lean_ctor_get(v_impl_2114_, 2);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_impl_2114_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2242_ = lean_ctor_get(v_impl_2114_, 4);
lean_dec(v_unused_2242_);
v_unused_2243_ = lean_ctor_get(v_impl_2114_, 3);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_impl_2114_, 0);
lean_dec(v_unused_2244_);
v___x_2232_ = v_impl_2114_;
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_v_2230_);
lean_inc(v_k_2229_);
lean_dec(v_impl_2114_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2241_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_unsigned_to_nat(3u);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 4, v_l_2199_);
lean_ctor_set(v___x_2232_, 2, v_v_1967_);
lean_ctor_set(v___x_2232_, 1, v_k_1966_);
lean_ctor_set(v___x_2232_, 0, v___x_2115_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_l_2199_);
lean_ctor_set(v_reuseFailAlloc_2240_, 4, v_l_2199_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_r_2228_);
lean_ctor_set(v___x_1971_, 3, v___x_2236_);
lean_ctor_set(v___x_1971_, 2, v_v_2230_);
lean_ctor_set(v___x_1971_, 1, v_k_2229_);
lean_ctor_set(v___x_1971_, 0, v___x_2234_);
v___x_2238_ = v___x_1971_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_k_2229_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_v_2230_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_r_2228_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(2u);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_impl_2114_);
lean_ctor_set(v___x_1971_, 3, v_r_2228_);
lean_ctor_set(v___x_1971_, 0, v___x_2245_);
v___x_2247_ = v___x_1971_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_r_2228_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_impl_2114_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
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
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v_k_1962_);
lean_ctor_set(v___x_2251_, 2, v_v_1963_);
lean_ctor_set(v___x_2251_, 3, v_t_1964_);
lean_ctor_set(v___x_2251_, 4, v_t_1964_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2252_, lean_object* v_x_2253_){
_start:
{
if (lean_obj_tag(v_x_2253_) == 0)
{
lean_object* v_k_2254_; lean_object* v_v_2255_; lean_object* v_l_2256_; lean_object* v_r_2257_; lean_object* v___x_2258_; 
v_k_2254_ = lean_ctor_get(v_x_2253_, 1);
lean_inc(v_k_2254_);
v_v_2255_ = lean_ctor_get(v_x_2253_, 2);
lean_inc(v_v_2255_);
v_l_2256_ = lean_ctor_get(v_x_2253_, 3);
lean_inc(v_l_2256_);
v_r_2257_ = lean_ctor_get(v_x_2253_, 4);
lean_inc(v_r_2257_);
lean_dec_ref_known(v_x_2253_, 5);
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2252_, v_l_2256_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_dec(v_r_2257_);
lean_dec(v_v_2255_);
lean_dec(v_k_2254_);
return v___x_2258_;
}
else
{
if (lean_obj_tag(v_v_2255_) == 4)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2373_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2373_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2373_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_elems_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_elems_2263_ = lean_ctor_get(v_v_2255_, 0);
lean_inc_ref(v_elems_2263_);
lean_dec_ref_known(v_v_2255_, 1);
v___x_2264_ = lean_array_get_size(v_elems_2263_);
v___x_2265_ = lean_unsigned_to_nat(8u);
v___x_2266_ = lean_nat_dec_eq(v___x_2264_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v___x_2267_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2268_ = l_Nat_reprFast(v___x_2264_);
v___x_2269_ = lean_string_append(v___x_2267_, v___x_2268_);
lean_dec_ref(v___x_2268_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2269_);
v___x_2271_ = v___x_2261_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_del_object(v___x_2261_);
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2274_);
lean_inc(v___x_2275_);
v___x_2276_ = l_Lean_Json_getNat_x3f(v___x_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_a_2285_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2286_);
lean_inc(v___x_2287_);
v___x_2288_ = l_Lean_Json_getNat_x3f(v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_a_2297_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2298_ = lean_unsigned_to_nat(2u);
v___x_2299_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2298_);
lean_inc(v___x_2299_);
v___x_2300_ = l_Lean_Json_getNat_x3f(v___x_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2309_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2310_ = lean_unsigned_to_nat(3u);
v___x_2311_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2310_);
lean_inc(v___x_2311_);
v___x_2312_ = l_Lean_Json_getNat_x3f(v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2309_);
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2321_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2322_ = lean_unsigned_to_nat(4u);
v___x_2323_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2322_);
lean_inc(v___x_2323_);
v___x_2324_ = l_Lean_Json_getNat_x3f(v___x_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2321_);
lean_dec(v_a_2309_);
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2333_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2334_ = lean_unsigned_to_nat(5u);
v___x_2335_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2334_);
lean_inc(v___x_2335_);
v___x_2336_ = l_Lean_Json_getNat_x3f(v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2333_);
lean_dec(v_a_2321_);
lean_dec(v_a_2309_);
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2346_ = lean_unsigned_to_nat(6u);
v___x_2347_ = lean_array_get_borrowed(v___x_2273_, v_elems_2263_, v___x_2346_);
lean_inc(v___x_2347_);
v___x_2348_ = l_Lean_Json_getNat_x3f(v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2345_);
lean_dec(v_a_2333_);
lean_dec(v_a_2321_);
lean_dec(v_a_2309_);
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec_ref(v_elems_2263_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_a_2357_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2358_ = lean_unsigned_to_nat(7u);
v___x_2359_ = lean_array_get(v___x_2273_, v_elems_2263_, v___x_2358_);
lean_dec_ref(v_elems_2263_);
v___x_2360_ = l_Lean_Json_getNat_x3f(v___x_2359_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v_a_2357_);
lean_dec(v_a_2345_);
lean_dec(v_a_2333_);
lean_dec(v_a_2321_);
lean_dec(v_a_2309_);
lean_dec(v_a_2297_);
lean_dec(v_a_2285_);
lean_dec(v_a_2259_);
lean_dec(v_r_2257_);
lean_dec(v_k_2254_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2369_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2370_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2370_, 0, v_a_2285_);
lean_ctor_set(v___x_2370_, 1, v_a_2297_);
lean_ctor_set(v___x_2370_, 2, v_a_2309_);
lean_ctor_set(v___x_2370_, 3, v_a_2321_);
lean_ctor_set(v___x_2370_, 4, v_a_2333_);
lean_ctor_set(v___x_2370_, 5, v_a_2345_);
lean_ctor_set(v___x_2370_, 6, v_a_2357_);
lean_ctor_set(v___x_2370_, 7, v_a_2369_);
v___x_2371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2254_, v___x_2370_, v_a_2259_);
v_init_2252_ = v___x_2371_;
v_x_2253_ = v_r_2257_;
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
lean_object* v___x_2374_; 
lean_dec_ref_known(v___x_2258_, 1);
lean_dec(v_r_2257_);
lean_dec(v_v_2255_);
lean_dec(v_k_2254_);
v___x_2374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2374_;
}
}
}
else
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_init_2252_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2394_, size_t v_i_2395_, lean_object* v_bs_2396_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2394_ = stack[0].m_num;
size_t v_i_2395_ = stack[1].m_num;
lean_object* v_bs_2396_ = stack[2].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2394_, v_i_2395_, v_bs_2396_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2407_, lean_object* v_i_2408_, lean_object* v_bs_2409_){
_start:
{
size_t v_sz_boxed_2410_; size_t v_i_boxed_2411_; lean_object* v_res_2412_; 
v_sz_boxed_2410_ = lean_unbox_usize(v_sz_2407_);
lean_dec(v_sz_2407_);
v_i_boxed_2411_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_res_2412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2410_, v_i_boxed_2411_, v_bs_2409_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2413_){
_start:
{
if (lean_obj_tag(v_x_2413_) == 4)
{
lean_object* v_elems_2414_; size_t v_sz_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v_elems_2414_ = lean_ctor_get(v_x_2413_, 0);
lean_inc_ref(v_elems_2414_);
lean_dec_ref_known(v_x_2413_, 1);
v_sz_2415_ = lean_array_size(v_elems_2414_);
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2415_, v___x_2416_, v_elems_2414_);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2418_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2419_ = lean_unsigned_to_nat(80u);
v___x_2420_ = l_Lean_Json_pretty(v_x_2413_, v___x_2419_);
v___x_2421_ = lean_string_append(v___x_2418_, v___x_2420_);
lean_dec_ref(v___x_2420_);
v___x_2422_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2423_ = lean_string_append(v___x_2421_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2427_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2446_; 
v_a_2438_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2440_ = v___x_2429_;
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2429_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2446_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2447_, lean_object* v_k_2448_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = l_Lean_Json_getObjValD(v_j_2447_, v_k_2448_);
v___x_2450_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2451_, lean_object* v_k_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2451_, v_k_2452_);
lean_dec_ref(v_k_2452_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2454_, lean_object* v_v_2455_, lean_object* v_t_2456_){
_start:
{
if (lean_obj_tag(v_t_2456_) == 0)
{
lean_object* v_size_2457_; lean_object* v_k_2458_; lean_object* v_v_2459_; lean_object* v_l_2460_; lean_object* v_r_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2741_; 
v_size_2457_ = lean_ctor_get(v_t_2456_, 0);
v_k_2458_ = lean_ctor_get(v_t_2456_, 1);
v_v_2459_ = lean_ctor_get(v_t_2456_, 2);
v_l_2460_ = lean_ctor_get(v_t_2456_, 3);
v_r_2461_ = lean_ctor_get(v_t_2456_, 4);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_t_2456_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2463_ = v_t_2456_;
v_isShared_2464_ = v_isSharedCheck_2741_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_r_2461_);
lean_inc(v_l_2460_);
lean_inc(v_v_2459_);
lean_inc(v_k_2458_);
lean_inc(v_size_2457_);
lean_dec(v_t_2456_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2741_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
uint8_t v___x_2465_; 
v___x_2465_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2454_, v_k_2458_);
switch(v___x_2465_)
{
case 0:
{
lean_object* v_impl_2466_; lean_object* v___x_2467_; 
lean_dec(v_size_2457_);
v_impl_2466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2454_, v_v_2455_, v_l_2460_);
v___x_2467_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2461_) == 0)
{
lean_object* v_size_2468_; lean_object* v_size_2469_; lean_object* v_k_2470_; lean_object* v_v_2471_; lean_object* v_l_2472_; lean_object* v_r_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_size_2468_ = lean_ctor_get(v_r_2461_, 0);
v_size_2469_ = lean_ctor_get(v_impl_2466_, 0);
v_k_2470_ = lean_ctor_get(v_impl_2466_, 1);
v_v_2471_ = lean_ctor_get(v_impl_2466_, 2);
v_l_2472_ = lean_ctor_get(v_impl_2466_, 3);
v_r_2473_ = lean_ctor_get(v_impl_2466_, 4);
lean_inc(v_r_2473_);
v___x_2474_ = lean_unsigned_to_nat(3u);
v___x_2475_ = lean_nat_mul(v___x_2474_, v_size_2468_);
v___x_2476_ = lean_nat_dec_lt(v___x_2475_, v_size_2469_);
lean_dec(v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_dec(v_r_2473_);
v___x_2477_ = lean_nat_add(v___x_2467_, v_size_2469_);
v___x_2478_ = lean_nat_add(v___x_2477_, v_size_2468_);
lean_dec(v___x_2477_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 3, v_impl_2466_);
lean_ctor_set(v___x_2463_, 0, v___x_2478_);
v___x_2480_ = v___x_2463_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v_impl_2466_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_r_2461_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
else
{
lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2547_; 
lean_inc(v_l_2472_);
lean_inc(v_v_2471_);
lean_inc(v_k_2470_);
lean_inc(v_size_2469_);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_impl_2466_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; lean_object* v_unused_2551_; lean_object* v_unused_2552_; 
v_unused_2548_ = lean_ctor_get(v_impl_2466_, 4);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_impl_2466_, 3);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_impl_2466_, 2);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_impl_2466_, 1);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_impl_2466_, 0);
lean_dec(v_unused_2552_);
v___x_2483_ = v_impl_2466_;
v_isShared_2484_ = v_isSharedCheck_2547_;
goto v_resetjp_2482_;
}
else
{
lean_dec(v_impl_2466_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2547_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_size_2485_; lean_object* v_size_2486_; lean_object* v_k_2487_; lean_object* v_v_2488_; lean_object* v_l_2489_; lean_object* v_r_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v_size_2485_ = lean_ctor_get(v_l_2472_, 0);
v_size_2486_ = lean_ctor_get(v_r_2473_, 0);
v_k_2487_ = lean_ctor_get(v_r_2473_, 1);
v_v_2488_ = lean_ctor_get(v_r_2473_, 2);
v_l_2489_ = lean_ctor_get(v_r_2473_, 3);
v_r_2490_ = lean_ctor_get(v_r_2473_, 4);
v___x_2491_ = lean_unsigned_to_nat(2u);
v___x_2492_ = lean_nat_mul(v___x_2491_, v_size_2485_);
v___x_2493_ = lean_nat_dec_lt(v_size_2486_, v___x_2492_);
lean_dec(v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2522_; 
lean_inc(v_r_2490_);
lean_inc(v_l_2489_);
lean_inc(v_v_2488_);
lean_inc(v_k_2487_);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_r_2473_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; lean_object* v_unused_2524_; lean_object* v_unused_2525_; lean_object* v_unused_2526_; lean_object* v_unused_2527_; 
v_unused_2523_ = lean_ctor_get(v_r_2473_, 4);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_r_2473_, 3);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_r_2473_, 2);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v_r_2473_, 1);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_r_2473_, 0);
lean_dec(v_unused_2527_);
v___x_2495_ = v_r_2473_;
v_isShared_2496_ = v_isSharedCheck_2522_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v_r_2473_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2522_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___x_2510_; lean_object* v___y_2512_; 
v___x_2497_ = lean_nat_add(v___x_2467_, v_size_2469_);
lean_dec(v_size_2469_);
v___x_2498_ = lean_nat_add(v___x_2497_, v_size_2468_);
lean_dec(v___x_2497_);
v___x_2510_ = lean_nat_add(v___x_2467_, v_size_2485_);
if (lean_obj_tag(v_l_2489_) == 0)
{
lean_object* v_size_2520_; 
v_size_2520_ = lean_ctor_get(v_l_2489_, 0);
lean_inc(v_size_2520_);
v___y_2512_ = v_size_2520_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___y_2512_ = v___x_2521_;
goto v___jp_2511_;
}
v___jp_2499_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_nat_add(v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec(v___y_2501_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 4, v_r_2461_);
lean_ctor_set(v___x_2495_, 3, v_r_2490_);
lean_ctor_set(v___x_2495_, 2, v_v_2459_);
lean_ctor_set(v___x_2495_, 1, v_k_2458_);
lean_ctor_set(v___x_2495_, 0, v___x_2503_);
v___x_2505_ = v___x_2495_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_r_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_r_2461_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 4, v___x_2505_);
lean_ctor_set(v___x_2483_, 3, v___y_2500_);
lean_ctor_set(v___x_2483_, 2, v_v_2488_);
lean_ctor_set(v___x_2483_, 1, v_k_2487_);
lean_ctor_set(v___x_2483_, 0, v___x_2498_);
v___x_2507_ = v___x_2483_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2487_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2488_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v___y_2500_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
v___jp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_nat_add(v___x_2510_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec(v___x_2510_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_l_2489_);
lean_ctor_set(v___x_2463_, 3, v_l_2472_);
lean_ctor_set(v___x_2463_, 2, v_v_2471_);
lean_ctor_set(v___x_2463_, 1, v_k_2470_);
lean_ctor_set(v___x_2463_, 0, v___x_2513_);
v___x_2515_ = v___x_2463_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_k_2470_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_v_2471_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_l_2472_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_l_2489_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_nat_add(v___x_2467_, v_size_2468_);
if (lean_obj_tag(v_r_2490_) == 0)
{
lean_object* v_size_2517_; 
v_size_2517_ = lean_ctor_get(v_r_2490_, 0);
lean_inc(v_size_2517_);
v___y_2500_ = v___x_2515_;
v___y_2501_ = v___x_2516_;
v___y_2502_ = v_size_2517_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_unsigned_to_nat(0u);
v___y_2500_ = v___x_2515_;
v___y_2501_ = v___x_2516_;
v___y_2502_ = v___x_2518_;
goto v___jp_2499_;
}
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
lean_del_object(v___x_2463_);
v___x_2528_ = lean_nat_add(v___x_2467_, v_size_2469_);
lean_dec(v_size_2469_);
v___x_2529_ = lean_nat_add(v___x_2528_, v_size_2468_);
lean_dec(v___x_2528_);
v___x_2530_ = lean_nat_add(v___x_2467_, v_size_2468_);
v___x_2531_ = lean_nat_add(v___x_2530_, v_size_2486_);
lean_dec(v___x_2530_);
lean_inc_ref(v_r_2461_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 4, v_r_2461_);
lean_ctor_set(v___x_2483_, 3, v_r_2473_);
lean_ctor_set(v___x_2483_, 2, v_v_2459_);
lean_ctor_set(v___x_2483_, 1, v_k_2458_);
lean_ctor_set(v___x_2483_, 0, v___x_2531_);
v___x_2533_ = v___x_2483_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_r_2473_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_r_2461_);
v___x_2533_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_isSharedCheck_2540_ = !lean_is_exclusive(v_r_2461_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; lean_object* v_unused_2544_; lean_object* v_unused_2545_; 
v_unused_2541_ = lean_ctor_get(v_r_2461_, 4);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_r_2461_, 3);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_r_2461_, 2);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_r_2461_, 1);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_r_2461_, 0);
lean_dec(v_unused_2545_);
v___x_2535_ = v_r_2461_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v_r_2461_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 4, v___x_2533_);
lean_ctor_set(v___x_2535_, 3, v_l_2472_);
lean_ctor_set(v___x_2535_, 2, v_v_2471_);
lean_ctor_set(v___x_2535_, 1, v_k_2470_);
lean_ctor_set(v___x_2535_, 0, v___x_2529_);
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2470_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2471_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_l_2472_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2553_; 
v_l_2553_ = lean_ctor_get(v_impl_2466_, 3);
if (lean_obj_tag(v_l_2553_) == 0)
{
lean_object* v_r_2554_; lean_object* v_k_2555_; lean_object* v_v_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2567_; 
lean_inc_ref(v_l_2553_);
v_r_2554_ = lean_ctor_get(v_impl_2466_, 4);
v_k_2555_ = lean_ctor_get(v_impl_2466_, 1);
v_v_2556_ = lean_ctor_get(v_impl_2466_, 2);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_impl_2466_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; lean_object* v_unused_2569_; 
v_unused_2568_ = lean_ctor_get(v_impl_2466_, 3);
lean_dec(v_unused_2568_);
v_unused_2569_ = lean_ctor_get(v_impl_2466_, 0);
lean_dec(v_unused_2569_);
v___x_2558_ = v_impl_2466_;
v_isShared_2559_ = v_isSharedCheck_2567_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_r_2554_);
lean_inc(v_v_2556_);
lean_inc(v_k_2555_);
lean_dec(v_impl_2466_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2567_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2554_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 3, v_r_2554_);
lean_ctor_set(v___x_2558_, 2, v_v_2459_);
lean_ctor_set(v___x_2558_, 1, v_k_2458_);
lean_ctor_set(v___x_2558_, 0, v___x_2467_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_r_2554_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_r_2554_);
v___x_2562_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v___x_2562_);
lean_ctor_set(v___x_2463_, 3, v_l_2553_);
lean_ctor_set(v___x_2463_, 2, v_v_2556_);
lean_ctor_set(v___x_2463_, 1, v_k_2555_);
lean_ctor_set(v___x_2463_, 0, v___x_2560_);
v___x_2564_ = v___x_2463_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2555_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2556_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_l_2553_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_r_2570_; 
v_r_2570_ = lean_ctor_get(v_impl_2466_, 4);
lean_inc(v_r_2570_);
if (lean_obj_tag(v_r_2570_) == 0)
{
lean_object* v_k_2571_; lean_object* v_v_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2595_; 
lean_inc(v_l_2553_);
v_k_2571_ = lean_ctor_get(v_impl_2466_, 1);
v_v_2572_ = lean_ctor_get(v_impl_2466_, 2);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_impl_2466_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; 
v_unused_2596_ = lean_ctor_get(v_impl_2466_, 4);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_impl_2466_, 3);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_impl_2466_, 0);
lean_dec(v_unused_2598_);
v___x_2574_ = v_impl_2466_;
v_isShared_2575_ = v_isSharedCheck_2595_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_v_2572_);
lean_inc(v_k_2571_);
lean_dec(v_impl_2466_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2595_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_k_2576_; lean_object* v_v_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2591_; 
v_k_2576_ = lean_ctor_get(v_r_2570_, 1);
v_v_2577_ = lean_ctor_get(v_r_2570_, 2);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_r_2570_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; lean_object* v_unused_2593_; lean_object* v_unused_2594_; 
v_unused_2592_ = lean_ctor_get(v_r_2570_, 4);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_r_2570_, 3);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_r_2570_, 0);
lean_dec(v_unused_2594_);
v___x_2579_ = v_r_2570_;
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_v_2577_);
lean_inc(v_k_2576_);
lean_dec(v_r_2570_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2591_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_unsigned_to_nat(3u);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_l_2553_);
lean_ctor_set(v___x_2579_, 3, v_l_2553_);
lean_ctor_set(v___x_2579_, 2, v_v_2572_);
lean_ctor_set(v___x_2579_, 1, v_k_2571_);
lean_ctor_set(v___x_2579_, 0, v___x_2467_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2571_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2572_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_l_2553_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_l_2553_);
v___x_2583_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 4, v_l_2553_);
lean_ctor_set(v___x_2574_, 2, v_v_2459_);
lean_ctor_set(v___x_2574_, 1, v_k_2458_);
lean_ctor_set(v___x_2574_, 0, v___x_2467_);
v___x_2585_ = v___x_2574_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_l_2553_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_l_2553_);
v___x_2585_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2587_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v___x_2585_);
lean_ctor_set(v___x_2463_, 3, v___x_2583_);
lean_ctor_set(v___x_2463_, 2, v_v_2577_);
lean_ctor_set(v___x_2463_, 1, v_k_2576_);
lean_ctor_set(v___x_2463_, 0, v___x_2581_);
v___x_2587_ = v___x_2463_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_k_2576_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v_v_2577_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_unsigned_to_nat(2u);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_r_2570_);
lean_ctor_set(v___x_2463_, 3, v_impl_2466_);
lean_ctor_set(v___x_2463_, 0, v___x_2599_);
v___x_2601_ = v___x_2463_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_impl_2466_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_r_2570_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2604_; 
lean_dec(v_v_2459_);
lean_dec(v_k_2458_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 2, v_v_2455_);
lean_ctor_set(v___x_2463_, 1, v_k_2454_);
v___x_2604_ = v___x_2463_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_size_2457_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_k_2454_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_v_2455_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_l_2460_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_r_2461_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
default: 
{
lean_object* v_impl_2606_; lean_object* v___x_2607_; 
lean_dec(v_size_2457_);
v_impl_2606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2454_, v_v_2455_, v_r_2461_);
v___x_2607_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2460_) == 0)
{
lean_object* v_size_2608_; lean_object* v_size_2609_; lean_object* v_k_2610_; lean_object* v_v_2611_; lean_object* v_l_2612_; lean_object* v_r_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_size_2608_ = lean_ctor_get(v_l_2460_, 0);
v_size_2609_ = lean_ctor_get(v_impl_2606_, 0);
v_k_2610_ = lean_ctor_get(v_impl_2606_, 1);
v_v_2611_ = lean_ctor_get(v_impl_2606_, 2);
v_l_2612_ = lean_ctor_get(v_impl_2606_, 3);
lean_inc(v_l_2612_);
v_r_2613_ = lean_ctor_get(v_impl_2606_, 4);
v___x_2614_ = lean_unsigned_to_nat(3u);
v___x_2615_ = lean_nat_mul(v___x_2614_, v_size_2608_);
v___x_2616_ = lean_nat_dec_lt(v___x_2615_, v_size_2609_);
lean_dec(v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
lean_dec(v_l_2612_);
v___x_2617_ = lean_nat_add(v___x_2607_, v_size_2608_);
v___x_2618_ = lean_nat_add(v___x_2617_, v_size_2609_);
lean_dec(v___x_2617_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_impl_2606_);
lean_ctor_set(v___x_2463_, 0, v___x_2618_);
v___x_2620_ = v___x_2463_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_l_2460_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v_impl_2606_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2685_; 
lean_inc(v_r_2613_);
lean_inc(v_v_2611_);
lean_inc(v_k_2610_);
lean_inc(v_size_2609_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_impl_2606_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; lean_object* v_unused_2690_; 
v_unused_2686_ = lean_ctor_get(v_impl_2606_, 4);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_impl_2606_, 3);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_impl_2606_, 2);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_impl_2606_, 1);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_impl_2606_, 0);
lean_dec(v_unused_2690_);
v___x_2623_ = v_impl_2606_;
v_isShared_2624_ = v_isSharedCheck_2685_;
goto v_resetjp_2622_;
}
else
{
lean_dec(v_impl_2606_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2685_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_size_2625_; lean_object* v_k_2626_; lean_object* v_v_2627_; lean_object* v_l_2628_; lean_object* v_r_2629_; lean_object* v_size_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_size_2625_ = lean_ctor_get(v_l_2612_, 0);
v_k_2626_ = lean_ctor_get(v_l_2612_, 1);
v_v_2627_ = lean_ctor_get(v_l_2612_, 2);
v_l_2628_ = lean_ctor_get(v_l_2612_, 3);
v_r_2629_ = lean_ctor_get(v_l_2612_, 4);
v_size_2630_ = lean_ctor_get(v_r_2613_, 0);
v___x_2631_ = lean_unsigned_to_nat(2u);
v___x_2632_ = lean_nat_mul(v___x_2631_, v_size_2630_);
v___x_2633_ = lean_nat_dec_lt(v_size_2625_, v___x_2632_);
lean_dec(v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2661_; 
lean_inc(v_r_2629_);
lean_inc(v_l_2628_);
lean_inc(v_v_2627_);
lean_inc(v_k_2626_);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_l_2612_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; lean_object* v_unused_2666_; 
v_unused_2662_ = lean_ctor_get(v_l_2612_, 4);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_l_2612_, 3);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_l_2612_, 2);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_l_2612_, 1);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_l_2612_, 0);
lean_dec(v_unused_2666_);
v___x_2635_ = v_l_2612_;
v_isShared_2636_ = v_isSharedCheck_2661_;
goto v_resetjp_2634_;
}
else
{
lean_dec(v_l_2612_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2661_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2651_; 
v___x_2637_ = lean_nat_add(v___x_2607_, v_size_2608_);
v___x_2638_ = lean_nat_add(v___x_2637_, v_size_2609_);
lean_dec(v_size_2609_);
if (lean_obj_tag(v_l_2628_) == 0)
{
lean_object* v_size_2659_; 
v_size_2659_ = lean_ctor_get(v_l_2628_, 0);
lean_inc(v_size_2659_);
v___y_2651_ = v_size_2659_;
goto v___jp_2650_;
}
else
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___y_2651_ = v___x_2660_;
goto v___jp_2650_;
}
v___jp_2639_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_nat_add(v___y_2640_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec(v___y_2640_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 4, v_r_2613_);
lean_ctor_set(v___x_2635_, 3, v_r_2629_);
lean_ctor_set(v___x_2635_, 2, v_v_2611_);
lean_ctor_set(v___x_2635_, 1, v_k_2610_);
lean_ctor_set(v___x_2635_, 0, v___x_2643_);
v___x_2645_ = v___x_2635_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_k_2610_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_v_2611_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_r_2629_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_r_2613_);
v___x_2645_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2647_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 4, v___x_2645_);
lean_ctor_set(v___x_2623_, 3, v___y_2641_);
lean_ctor_set(v___x_2623_, 2, v_v_2627_);
lean_ctor_set(v___x_2623_, 1, v_k_2626_);
lean_ctor_set(v___x_2623_, 0, v___x_2638_);
v___x_2647_ = v___x_2623_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2626_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2627_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v___y_2641_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
v___jp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = lean_nat_add(v___x_2637_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec(v___x_2637_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_l_2628_);
lean_ctor_set(v___x_2463_, 0, v___x_2652_);
v___x_2654_ = v___x_2463_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2658_, 3, v_l_2460_);
lean_ctor_set(v_reuseFailAlloc_2658_, 4, v_l_2628_);
v___x_2654_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_nat_add(v___x_2607_, v_size_2630_);
if (lean_obj_tag(v_r_2629_) == 0)
{
lean_object* v_size_2656_; 
v_size_2656_ = lean_ctor_get(v_r_2629_, 0);
lean_inc(v_size_2656_);
v___y_2640_ = v___x_2655_;
v___y_2641_ = v___x_2654_;
v___y_2642_ = v_size_2656_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___y_2640_ = v___x_2655_;
v___y_2641_ = v___x_2654_;
v___y_2642_ = v___x_2657_;
goto v___jp_2639_;
}
}
}
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_del_object(v___x_2463_);
v___x_2667_ = lean_nat_add(v___x_2607_, v_size_2608_);
v___x_2668_ = lean_nat_add(v___x_2667_, v_size_2609_);
lean_dec(v_size_2609_);
v___x_2669_ = lean_nat_add(v___x_2667_, v_size_2625_);
lean_dec(v___x_2667_);
lean_inc_ref(v_l_2460_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 4, v_l_2612_);
lean_ctor_set(v___x_2623_, 3, v_l_2460_);
lean_ctor_set(v___x_2623_, 2, v_v_2459_);
lean_ctor_set(v___x_2623_, 1, v_k_2458_);
lean_ctor_set(v___x_2623_, 0, v___x_2669_);
v___x_2671_ = v___x_2623_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_l_2460_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_l_2612_);
v___x_2671_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_isSharedCheck_2678_ = !lean_is_exclusive(v_l_2460_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; lean_object* v_unused_2683_; 
v_unused_2679_ = lean_ctor_get(v_l_2460_, 4);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2460_, 3);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2460_, 2);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_l_2460_, 1);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_l_2460_, 0);
lean_dec(v_unused_2683_);
v___x_2673_ = v_l_2460_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v_l_2460_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 4, v_r_2613_);
lean_ctor_set(v___x_2673_, 3, v___x_2671_);
lean_ctor_set(v___x_2673_, 2, v_v_2611_);
lean_ctor_set(v___x_2673_, 1, v_k_2610_);
lean_ctor_set(v___x_2673_, 0, v___x_2668_);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_k_2610_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_v_2611_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_r_2613_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2691_; 
v_l_2691_ = lean_ctor_get(v_impl_2606_, 3);
lean_inc(v_l_2691_);
if (lean_obj_tag(v_l_2691_) == 0)
{
lean_object* v_r_2692_; lean_object* v_k_2693_; lean_object* v_v_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2717_; 
v_r_2692_ = lean_ctor_get(v_impl_2606_, 4);
v_k_2693_ = lean_ctor_get(v_impl_2606_, 1);
v_v_2694_ = lean_ctor_get(v_impl_2606_, 2);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_impl_2606_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2718_ = lean_ctor_get(v_impl_2606_, 3);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_impl_2606_, 0);
lean_dec(v_unused_2719_);
v___x_2696_ = v_impl_2606_;
v_isShared_2697_ = v_isSharedCheck_2717_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_r_2692_);
lean_inc(v_v_2694_);
lean_inc(v_k_2693_);
lean_dec(v_impl_2606_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2717_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_k_2698_; lean_object* v_v_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2713_; 
v_k_2698_ = lean_ctor_get(v_l_2691_, 1);
v_v_2699_ = lean_ctor_get(v_l_2691_, 2);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_l_2691_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; lean_object* v_unused_2715_; lean_object* v_unused_2716_; 
v_unused_2714_ = lean_ctor_get(v_l_2691_, 4);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_l_2691_, 3);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_l_2691_, 0);
lean_dec(v_unused_2716_);
v___x_2701_ = v_l_2691_;
v_isShared_2702_ = v_isSharedCheck_2713_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_v_2699_);
lean_inc(v_k_2698_);
lean_dec(v_l_2691_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2713_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2692_, 2);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 4, v_r_2692_);
lean_ctor_set(v___x_2701_, 3, v_r_2692_);
lean_ctor_set(v___x_2701_, 2, v_v_2459_);
lean_ctor_set(v___x_2701_, 1, v_k_2458_);
lean_ctor_set(v___x_2701_, 0, v___x_2607_);
v___x_2705_ = v___x_2701_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_r_2692_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v_r_2692_);
v___x_2705_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2707_; 
lean_inc(v_r_2692_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 3, v_r_2692_);
lean_ctor_set(v___x_2696_, 0, v___x_2607_);
v___x_2707_ = v___x_2696_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_k_2693_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_v_2694_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_r_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_r_2692_);
v___x_2707_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v___x_2707_);
lean_ctor_set(v___x_2463_, 3, v___x_2705_);
lean_ctor_set(v___x_2463_, 2, v_v_2699_);
lean_ctor_set(v___x_2463_, 1, v_k_2698_);
lean_ctor_set(v___x_2463_, 0, v___x_2703_);
v___x_2709_ = v___x_2463_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2698_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2699_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
else
{
lean_object* v_r_2720_; 
v_r_2720_ = lean_ctor_get(v_impl_2606_, 4);
lean_inc(v_r_2720_);
if (lean_obj_tag(v_r_2720_) == 0)
{
lean_object* v_k_2721_; lean_object* v_v_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2733_; 
v_k_2721_ = lean_ctor_get(v_impl_2606_, 1);
v_v_2722_ = lean_ctor_get(v_impl_2606_, 2);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_impl_2606_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2734_ = lean_ctor_get(v_impl_2606_, 4);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_impl_2606_, 3);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_impl_2606_, 0);
lean_dec(v_unused_2736_);
v___x_2724_ = v_impl_2606_;
v_isShared_2725_ = v_isSharedCheck_2733_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_v_2722_);
lean_inc(v_k_2721_);
lean_dec(v_impl_2606_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2733_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_unsigned_to_nat(3u);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 4, v_l_2691_);
lean_ctor_set(v___x_2724_, 2, v_v_2459_);
lean_ctor_set(v___x_2724_, 1, v_k_2458_);
lean_ctor_set(v___x_2724_, 0, v___x_2607_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_l_2691_);
lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_l_2691_);
v___x_2728_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_r_2720_);
lean_ctor_set(v___x_2463_, 3, v___x_2728_);
lean_ctor_set(v___x_2463_, 2, v_v_2722_);
lean_ctor_set(v___x_2463_, 1, v_k_2721_);
lean_ctor_set(v___x_2463_, 0, v___x_2726_);
v___x_2730_ = v___x_2463_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_k_2721_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_v_2722_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2731_, 4, v_r_2720_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = lean_unsigned_to_nat(2u);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 4, v_impl_2606_);
lean_ctor_set(v___x_2463_, 3, v_r_2720_);
lean_ctor_set(v___x_2463_, 0, v___x_2737_);
v___x_2739_ = v___x_2463_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_k_2458_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_v_2459_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v_r_2720_);
lean_ctor_set(v_reuseFailAlloc_2740_, 4, v_impl_2606_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
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
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v_k_2454_);
lean_ctor_set(v___x_2743_, 2, v_v_2455_);
lean_ctor_set(v___x_2743_, 3, v_t_2456_);
lean_ctor_set(v___x_2743_, 4, v_t_2456_);
return v___x_2743_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2744_, size_t v_i_2745_, lean_object* v_bs_2746_){
_start:
{
uint8_t v___x_2747_; 
v___x_2747_ = lean_usize_dec_lt(v_i_2745_, v_sz_2744_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_bs_2746_);
return v___x_2748_;
}
else
{
lean_object* v_v_2749_; lean_object* v___x_2750_; lean_object* v_bs_x27_2751_; lean_object* v_a_2753_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2824_; 
v_v_2749_ = lean_array_uget(v_bs_2746_, v_i_2745_);
v___x_2750_ = lean_unsigned_to_nat(0u);
v_bs_x27_2751_ = lean_array_uset(v_bs_2746_, v_i_2745_, v___x_2750_);
v___x_2758_ = lean_array_get_size(v_v_2749_);
v___x_2759_ = lean_unsigned_to_nat(4u);
v___x_2824_ = lean_nat_dec_eq(v___x_2758_, v___x_2759_);
if (v___x_2824_ == 0)
{
if (v___x_2747_ == 0)
{
goto v___jp_2760_;
}
else
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_unsigned_to_nat(5u);
v___x_2826_ = lean_nat_dec_eq(v___x_2758_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_bs_x27_2751_);
lean_dec(v_v_2749_);
v___x_2827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2828_ = l_Nat_reprFast(v___x_2758_);
v___x_2829_ = lean_string_append(v___x_2827_, v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
goto v___jp_2760_;
}
}
}
else
{
goto v___jp_2760_;
}
v___jp_2752_:
{
size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = ((size_t)1ULL);
v___x_2755_ = lean_usize_add(v_i_2745_, v___x_2754_);
v___x_2756_ = lean_array_uset(v_bs_x27_2751_, v_i_2745_, v_a_2753_);
v_i_2745_ = v___x_2755_;
v_bs_2746_ = v___x_2756_;
goto _start;
}
v___jp_2760_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_array_fget_borrowed(v_v_2749_, v___x_2750_);
lean_inc(v___x_2761_);
v___x_2762_ = l_Lean_Json_getNat_x3f(v___x_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_bs_x27_2751_);
lean_dec(v_v_2749_);
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_a_2771_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_array_fget_borrowed(v_v_2749_, v___x_2772_);
lean_inc(v___x_2773_);
v___x_2774_ = l_Lean_Json_getNat_x3f(v___x_2773_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2771_);
lean_dec_ref(v_bs_x27_2751_);
lean_dec(v_v_2749_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2784_ = lean_unsigned_to_nat(2u);
v___x_2785_ = lean_array_fget_borrowed(v_v_2749_, v___x_2784_);
lean_inc(v___x_2785_);
v___x_2786_ = l_Lean_Json_getNat_x3f(v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2783_);
lean_dec(v_a_2771_);
lean_dec_ref(v_bs_x27_2751_);
lean_dec(v_v_2749_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2796_ = lean_unsigned_to_nat(3u);
v___x_2797_ = lean_array_fget_borrowed(v_v_2749_, v___x_2796_);
lean_inc(v___x_2797_);
v___x_2798_ = l_Lean_Json_getNat_x3f(v___x_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2795_);
lean_dec(v_a_2783_);
lean_dec(v_a_2771_);
lean_dec_ref(v_bs_x27_2751_);
lean_dec(v_v_2749_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_a_2807_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2808_ = lean_unsigned_to_nat(5u);
v___x_2809_ = lean_nat_dec_eq(v___x_2758_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec(v_v_2749_);
v___x_2810_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2771_);
lean_ctor_set(v___x_2811_, 1, v_a_2783_);
lean_ctor_set(v___x_2811_, 2, v_a_2795_);
lean_ctor_set(v___x_2811_, 3, v_a_2807_);
lean_ctor_set(v___x_2811_, 4, v___x_2810_);
v_a_2753_ = v___x_2811_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = lean_array_fget(v_v_2749_, v___x_2759_);
lean_dec(v_v_2749_);
v___x_2813_ = l_Lean_Json_getStr_x3f(v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2807_);
lean_dec(v_a_2795_);
lean_dec(v_a_2783_);
lean_dec(v_a_2771_);
lean_dec_ref(v_bs_x27_2751_);
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
lean_object* v_a_2822_; lean_object* v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2771_);
lean_ctor_set(v___x_2823_, 1, v_a_2783_);
lean_ctor_set(v___x_2823_, 2, v_a_2795_);
lean_ctor_set(v___x_2823_, 3, v_a_2807_);
lean_ctor_set(v___x_2823_, 4, v_a_2822_);
v_a_2753_ = v___x_2823_;
goto v___jp_2752_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2744_ = stack[0].m_num;
size_t v_i_2745_ = stack[1].m_num;
lean_object* v_bs_2746_ = stack[2].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2744_, v_i_2745_, v_bs_2746_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2832_, lean_object* v_i_2833_, lean_object* v_bs_2834_){
_start:
{
size_t v_sz_boxed_2835_; size_t v_i_boxed_2836_; lean_object* v_res_2837_; 
v_sz_boxed_2835_ = lean_unbox_usize(v_sz_2832_);
lean_dec(v_sz_2832_);
v_i_boxed_2836_ = lean_unbox_usize(v_i_2833_);
lean_dec(v_i_2833_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2835_, v_i_boxed_2836_, v_bs_2834_);
return v_res_2837_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2838_, size_t v_i_2839_, lean_object* v_bs_2840_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_lt(v_i_2839_, v_sz_2838_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_bs_2840_);
return v___x_2842_;
}
else
{
lean_object* v_v_2843_; lean_object* v___x_2844_; 
v_v_2843_ = lean_array_uget_borrowed(v_bs_2840_, v_i_2839_);
lean_inc(v_v_2843_);
v___x_2844_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2843_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_bs_2840_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v_bs_x27_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v_a_2853_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2854_ = lean_unsigned_to_nat(0u);
v_bs_x27_2855_ = lean_array_uset(v_bs_2840_, v_i_2839_, v___x_2854_);
v___x_2856_ = ((size_t)1ULL);
v___x_2857_ = lean_usize_add(v_i_2839_, v___x_2856_);
v___x_2858_ = lean_array_uset(v_bs_x27_2855_, v_i_2839_, v_a_2853_);
v_i_2839_ = v___x_2857_;
v_bs_2840_ = v___x_2858_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2838_ = stack[0].m_num;
size_t v_i_2839_ = stack[1].m_num;
lean_object* v_bs_2840_ = stack[2].m_obj;
lean_object* v_res_2860_;
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2838_, v_i_2839_, v_bs_2840_);
stack->m_obj
 = v_res_2860_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2861_, lean_object* v_i_2862_, lean_object* v_bs_2863_){
_start:
{
size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2861_);
lean_dec(v_sz_2861_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2864_, v_i_boxed_2865_, v_bs_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2867_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 4)
{
lean_object* v_elems_2868_; size_t v_sz_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v_elems_2868_ = lean_ctor_get(v_x_2867_, 0);
lean_inc_ref(v_elems_2868_);
lean_dec_ref_known(v_x_2867_, 1);
v_sz_2869_ = lean_array_size(v_elems_2868_);
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2869_, v___x_2870_, v_elems_2868_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2872_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2873_ = lean_unsigned_to_nat(80u);
v___x_2874_ = l_Lean_Json_pretty(v_x_2867_, v___x_2873_);
v___x_2875_ = lean_string_append(v___x_2872_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2877_ = lean_string_append(v___x_2875_, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2879_, lean_object* v_k_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = l_Lean_Json_getObjValD(v_j_2879_, v_k_2880_);
v___x_2882_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2883_, lean_object* v_k_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2883_, v_k_2884_);
lean_dec_ref(v_k_2884_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2886_, lean_object* v_x_2887_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 0)
{
lean_object* v_k_2888_; lean_object* v_v_2889_; lean_object* v_l_2890_; lean_object* v_r_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_3051_; 
v_k_2888_ = lean_ctor_get(v_x_2887_, 1);
v_v_2889_ = lean_ctor_get(v_x_2887_, 2);
v_l_2890_ = lean_ctor_get(v_x_2887_, 3);
v_r_2891_ = lean_ctor_get(v_x_2887_, 4);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_x_2887_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v_x_2887_, 0);
lean_dec(v_unused_3052_);
v___x_2893_ = v_x_2887_;
v_isShared_2894_ = v_isSharedCheck_3051_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_r_2891_);
lean_inc(v_l_2890_);
lean_inc(v_v_2889_);
lean_inc(v_k_2888_);
lean_dec(v_x_2887_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_3051_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2886_, v_l_2890_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
lean_dec(v_k_2888_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_3050_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_3050_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_3050_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Json_parse(v_k_2888_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2909_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2910_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v_definition_x3f_2921_; lean_object* v_a_2949_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2919_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2953_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2889_);
v___x_2954_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2889_, v___x_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3049_; 
v_a_2963_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_2965_ = v___x_2954_;
v_isShared_2966_ = v_isSharedCheck_3049_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2954_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3049_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
if (lean_obj_tag(v_a_2963_) == 0)
{
lean_object* v___x_2967_; 
lean_del_object(v___x_2965_);
lean_del_object(v___x_2898_);
lean_del_object(v___x_2893_);
v___x_2967_ = lean_box(0);
v_definition_x3f_2921_ = v___x_2967_;
goto v___jp_2920_;
}
else
{
lean_object* v_val_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_3040_; 
v_val_2968_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_val_2968_);
lean_dec_ref_known(v_a_2963_, 1);
v___x_2969_ = lean_array_get_size(v_val_2968_);
v___x_2970_ = lean_unsigned_to_nat(4u);
v___x_3040_ = lean_nat_dec_eq(v___x_2969_, v___x_2970_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(5u);
v___x_3042_ = lean_nat_dec_eq(v___x_2969_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_dec(v_val_2968_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v___x_3043_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3044_ = l_Nat_reprFast(v___x_2969_);
v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
lean_dec_ref(v___x_3044_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 0);
lean_ctor_set(v___x_2965_, 0, v___x_3045_);
v___x_3047_ = v___x_2965_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
else
{
lean_del_object(v___x_2965_);
goto v___jp_2971_;
}
}
else
{
lean_del_object(v___x_2965_);
goto v___jp_2971_;
}
v___jp_2971_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_array_fget_borrowed(v_val_2968_, v___x_2972_);
lean_inc(v___x_2973_);
v___x_2974_ = l_Lean_Json_getNat_x3f(v___x_2973_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_val_2968_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2983_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_array_fget_borrowed(v_val_2968_, v___x_2984_);
lean_inc(v___x_2985_);
v___x_2986_ = l_Lean_Json_getNat_x3f(v___x_2985_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v_a_2983_);
lean_dec(v_val_2968_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_a_2995_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2996_ = lean_unsigned_to_nat(2u);
v___x_2997_ = lean_array_fget_borrowed(v_val_2968_, v___x_2996_);
lean_inc(v___x_2997_);
v___x_2998_ = l_Lean_Json_getNat_x3f(v___x_2997_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2995_);
lean_dec(v_a_2983_);
lean_dec(v_val_2968_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3007_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3008_ = lean_unsigned_to_nat(3u);
v___x_3009_ = lean_array_fget_borrowed(v_val_2968_, v___x_3008_);
lean_inc(v___x_3009_);
v___x_3010_ = l_Lean_Json_getNat_x3f(v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_a_3007_);
lean_dec(v_a_2995_);
lean_dec(v_a_2983_);
lean_dec(v_val_2968_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3020_ = lean_unsigned_to_nat(5u);
v___x_3021_ = lean_nat_dec_eq(v___x_2969_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_val_2968_);
v___x_3022_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 4, v___x_3022_);
lean_ctor_set(v___x_2893_, 3, v_a_3019_);
lean_ctor_set(v___x_2893_, 2, v_a_3007_);
lean_ctor_set(v___x_2893_, 1, v_a_2995_);
lean_ctor_set(v___x_2893_, 0, v_a_2983_);
v___x_3024_ = v___x_2893_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_2983_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_a_2995_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_a_3007_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_a_3019_);
lean_ctor_set(v_reuseFailAlloc_3025_, 4, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v_a_2949_ = v___x_3024_;
goto v___jp_2948_;
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = lean_array_fget(v_val_2968_, v___x_2970_);
lean_dec(v_val_2968_);
v___x_3027_ = l_Lean_Json_getStr_x3f(v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_a_3019_);
lean_dec(v_a_3007_);
lean_dec(v_a_2995_);
lean_dec(v_a_2983_);
lean_dec(v_a_2919_);
lean_del_object(v___x_2898_);
lean_dec(v_a_2896_);
lean_del_object(v___x_2893_);
lean_dec(v_r_2891_);
lean_dec(v_v_2889_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3027_, 1);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 4, v_a_3036_);
lean_ctor_set(v___x_2893_, 3, v_a_3019_);
lean_ctor_set(v___x_2893_, 2, v_a_3007_);
lean_ctor_set(v___x_2893_, 1, v_a_2995_);
lean_ctor_set(v___x_2893_, 0, v_a_2983_);
v___x_3038_ = v___x_2893_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_2983_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_a_2995_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_a_3007_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_a_3019_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v_a_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
v_a_2949_ = v___x_3038_;
goto v___jp_2948_;
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
v___jp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2889_, v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_definition_x3f_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2896_);
lean_dec(v_r_2891_);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2932_; size_t v_sz_2933_; size_t v___x_2934_; lean_object* v___x_2935_; 
v_a_2932_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2923_, 1);
v_sz_2933_ = lean_array_size(v_a_2932_);
v___x_2934_ = ((size_t)0ULL);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2933_, v___x_2934_, v_a_2932_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_definition_x3f_2921_);
lean_dec(v_a_2919_);
lean_dec(v_a_2896_);
lean_dec(v_r_2891_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2944_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_definition_x3f_2921_);
lean_ctor_set(v___x_2945_, 1, v_a_2944_);
v___x_2946_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2919_, v___x_2945_, v_a_2896_);
v_init_2886_ = v___x_2946_;
v_x_2887_ = v_r_2891_;
goto _start;
}
}
}
v___jp_2948_:
{
lean_object* v___x_2951_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_a_2949_);
v___x_2951_ = v___x_2898_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
v_definition_x3f_2921_ = v___x_2951_;
goto v___jp_2920_;
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
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_init_2886_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3054_, lean_object* v_k_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = l_Lean_Json_getObjValD(v_j_3054_, v_k_3055_);
v___x_3057_ = l_Lean_Json_getObj_x3f(v___x_3056_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_a_3066_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3067_ = lean_box(1);
v___x_3068_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3067_, v_a_3066_);
return v___x_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3069_, lean_object* v_k_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3069_, v_k_3070_);
lean_dec_ref(v_k_3070_);
return v_res_3071_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = 1;
v___x_3078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3082_ = lean_string_append(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3085_ = lean_string_append(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3087_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3088_ = lean_string_append(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = 1;
v___x_3093_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3094_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3096_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3097_ = lean_string_append(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3099_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3100_ = lean_string_append(v___x_3099_, v___x_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = 1;
v___x_3105_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3105_, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3109_ = lean_string_append(v___x_3108_, v___x_3107_);
return v___x_3109_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3111_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3112_ = lean_string_append(v___x_3111_, v___x_3110_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3113_){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3113_);
v___x_3115_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3113_, v___x_3114_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_json_3113_);
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3125_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3125_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3120_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3121_ = lean_string_append(v___x_3120_, v_a_3116_);
lean_dec(v_a_3116_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3121_);
v___x_3123_ = v___x_3118_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_json_3113_);
v_a_3126_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3115_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3115_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set_tag(v___x_3128_, 0);
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_a_3134_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3113_);
v___x_3136_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3113_, v___x_3135_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_a_3134_);
lean_dec(v_json_3113_);
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3146_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3146_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3142_ = lean_string_append(v___x_3141_, v_a_3137_);
lean_dec(v_a_3137_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3142_);
v___x_3144_ = v___x_3139_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_3134_);
lean_dec(v_json_3113_);
v_a_3147_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3136_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3136_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 0);
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3136_, 1);
v___x_3156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3113_, v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3155_);
lean_dec(v_a_3134_);
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3167_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3167_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3163_ = lean_string_append(v___x_3162_, v_a_3158_);
lean_dec(v_a_3158_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3163_);
v___x_3165_ = v___x_3160_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
else
{
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_3155_);
lean_dec(v_a_3134_);
v_a_3168_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3157_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3157_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 0);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3184_; 
v_a_3176_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3178_ = v___x_3157_;
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3157_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3184_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3180_, 0, v_a_3134_);
lean_ctor_set(v___x_3180_, 1, v_a_3155_);
lean_ctor_set(v___x_3180_, 2, v_a_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3185_, lean_object* v_k_3186_, lean_object* v_v_3187_, lean_object* v_t_3188_, lean_object* v_hl_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3186_, v_v_3187_, v_t_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3191_, lean_object* v_k_3192_, lean_object* v_v_3193_, lean_object* v_t_3194_, lean_object* v_hl_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3192_, v_v_3193_, v_t_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3199_, lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_object* v_k_3201_; lean_object* v_v_3202_; lean_object* v_l_3203_; lean_object* v_r_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_k_3201_ = lean_ctor_get(v_x_3200_, 1);
v_v_3202_ = lean_ctor_get(v_x_3200_, 2);
v_l_3203_ = lean_ctor_get(v_x_3200_, 3);
v_r_3204_ = lean_ctor_get(v_x_3200_, 4);
v___x_3205_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3199_, v_r_3204_);
lean_inc(v_v_3202_);
lean_inc(v_k_3201_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_k_3201_);
lean_ctor_set(v___x_3206_, 1, v_v_3202_);
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v___x_3205_);
v_init_3199_ = v___x_3207_;
v_x_3200_ = v_l_3203_;
goto _start;
}
else
{
return v_init_3199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3209_, v_x_3210_);
lean_dec(v_x_3210_);
return v_res_3211_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_bs_3214_){
_start:
{
uint8_t v___x_3215_; 
v___x_3215_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3215_ == 0)
{
return v_bs_3214_;
}
else
{
lean_object* v_v_3216_; lean_object* v___x_3217_; lean_object* v_bs_x27_3218_; size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v_v_3216_ = lean_array_uget(v_bs_3214_, v_i_3213_);
v___x_3217_ = lean_unsigned_to_nat(0u);
v_bs_x27_3218_ = lean_array_uset(v_bs_3214_, v_i_3213_, v___x_3217_);
v___x_3219_ = ((size_t)1ULL);
v___x_3220_ = lean_usize_add(v_i_3213_, v___x_3219_);
v___x_3221_ = lean_array_uset(v_bs_x27_3218_, v_i_3213_, v_v_3216_);
v_i_3213_ = v___x_3220_;
v_bs_3214_ = v___x_3221_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3212_ = stack[0].m_num;
size_t v_i_3213_ = stack[1].m_num;
lean_object* v_bs_3214_ = stack[2].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3212_, v_i_3213_, v_bs_3214_);
stack->m_obj
 = v_res_3223_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_bs_3226_){
_start:
{
size_t v_sz_boxed_3227_; size_t v_i_boxed_3228_; lean_object* v_res_3229_; 
v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3228_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3227_, v_i_boxed_3228_, v_bs_3226_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3230_){
_start:
{
size_t v_sz_3231_; size_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_sz_3231_ = lean_array_size(v_a_3230_);
v___x_3232_ = ((size_t)0ULL);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3231_, v___x_3232_, v_a_3230_);
v___x_3234_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_array_mk(v_a_3235_);
v___x_3237_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3238_){
_start:
{
if (lean_obj_tag(v_x_3238_) == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_box(0);
return v___x_3239_;
}
else
{
lean_object* v_val_3240_; lean_object* v___x_3241_; 
v_val_3240_ = lean_ctor_get(v_x_3238_, 0);
lean_inc(v_val_3240_);
lean_dec_ref_known(v_x_3238_, 1);
v___x_3241_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3240_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
if (lean_obj_tag(v_a_3242_) == 0)
{
lean_object* v___x_3244_; 
v___x_3244_ = l_List_reverse___redArg(v_a_3243_);
return v___x_3244_;
}
else
{
lean_object* v_head_3245_; lean_object* v_tail_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3256_; 
v_head_3245_ = lean_ctor_get(v_a_3242_, 0);
v_tail_3246_ = lean_ctor_get(v_a_3242_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_a_3242_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3248_ = v_a_3242_;
v_isShared_3249_ = v_isSharedCheck_3256_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_tail_3246_);
lean_inc(v_head_3245_);
lean_dec(v_a_3242_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3256_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3250_ = l_Lean_JsonNumber_fromNat(v_head_3245_);
v___x_3251_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v_a_3243_);
lean_ctor_set(v___x_3248_, 0, v___x_3251_);
v___x_3253_ = v___x_3248_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_a_3243_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
v_a_3242_ = v_tail_3246_;
v_a_3243_ = v___x_3253_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3257_, size_t v_i_3258_, lean_object* v_bs_3259_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = lean_usize_dec_lt(v_i_3258_, v_sz_3257_);
if (v___x_3260_ == 0)
{
return v_bs_3259_;
}
else
{
lean_object* v_v_3261_; lean_object* v_startPosLine_3262_; lean_object* v_startPosCharacter_3263_; lean_object* v_endPosLine_3264_; lean_object* v_endPosCharacter_3265_; lean_object* v___x_3266_; lean_object* v_bs_x27_3267_; lean_object* v___y_3269_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v_range_3279_; lean_object* v___x_3280_; 
v_v_3261_ = lean_array_uget(v_bs_3259_, v_i_3258_);
v_startPosLine_3262_ = lean_ctor_get(v_v_3261_, 0);
v_startPosCharacter_3263_ = lean_ctor_get(v_v_3261_, 1);
v_endPosLine_3264_ = lean_ctor_get(v_v_3261_, 2);
v_endPosCharacter_3265_ = lean_ctor_get(v_v_3261_, 3);
v___x_3266_ = lean_unsigned_to_nat(0u);
v_bs_x27_3267_ = lean_array_uset(v_bs_3259_, v_i_3258_, v___x_3266_);
v___x_3274_ = lean_box(0);
lean_inc(v_endPosCharacter_3265_);
v___x_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3275_, 0, v_endPosCharacter_3265_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
lean_inc(v_endPosLine_3264_);
v___x_3276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_endPosLine_3264_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
lean_inc(v_startPosCharacter_3263_);
v___x_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_startPosCharacter_3263_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
lean_inc(v_startPosLine_3262_);
v___x_3278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3278_, 0, v_startPosLine_3262_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v_range_3279_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3278_, v___x_3274_);
v___x_3280_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3261_);
lean_dec(v_v_3261_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = l_List_appendTR___redArg(v_range_3279_, v___x_3274_);
v___y_3269_ = v___x_3281_;
goto v___jp_3268_;
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3291_; 
v_val_3282_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3284_ = v___x_3280_;
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_val_3282_);
lean_dec(v___x_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 3);
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_val_3282_);
v___x_3287_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v___x_3274_);
v___x_3289_ = l_List_appendTR___redArg(v_range_3279_, v___x_3288_);
v___y_3269_ = v___x_3289_;
goto v___jp_3268_;
}
}
}
v___jp_3268_:
{
size_t v___x_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = ((size_t)1ULL);
v___x_3271_ = lean_usize_add(v_i_3258_, v___x_3270_);
v___x_3272_ = lean_array_uset(v_bs_x27_3267_, v_i_3258_, v___y_3269_);
v_i_3258_ = v___x_3271_;
v_bs_3259_ = v___x_3272_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3257_ = stack[0].m_num;
size_t v_i_3258_ = stack[1].m_num;
lean_object* v_bs_3259_ = stack[2].m_obj;
lean_object* v_res_3292_;
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3257_, v_i_3258_, v_bs_3259_);
stack->m_obj
 = v_res_3292_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_bs_3295_){
_start:
{
size_t v_sz_boxed_3296_; size_t v_i_boxed_3297_; lean_object* v_res_3298_; 
v_sz_boxed_3296_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3297_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3296_, v_i_boxed_3297_, v_bs_3295_);
return v_res_3298_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3299_, size_t v_i_3300_, lean_object* v_bs_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
if (v___x_3302_ == 0)
{
return v_bs_3301_;
}
else
{
lean_object* v_v_3303_; lean_object* v___x_3304_; lean_object* v_bs_x27_3305_; lean_object* v___x_3306_; size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
v_v_3303_ = lean_array_uget(v_bs_3301_, v_i_3300_);
v___x_3304_ = lean_unsigned_to_nat(0u);
v_bs_x27_3305_ = lean_array_uset(v_bs_3301_, v_i_3300_, v___x_3304_);
v___x_3306_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3303_);
v___x_3307_ = ((size_t)1ULL);
v___x_3308_ = lean_usize_add(v_i_3300_, v___x_3307_);
v___x_3309_ = lean_array_uset(v_bs_x27_3305_, v_i_3300_, v___x_3306_);
v_i_3300_ = v___x_3308_;
v_bs_3301_ = v___x_3309_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3299_ = stack[0].m_num;
size_t v_i_3300_ = stack[1].m_num;
lean_object* v_bs_3301_ = stack[2].m_obj;
lean_object* v_res_3311_;
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3299_, v_i_3300_, v_bs_3301_);
stack->m_obj
 = v_res_3311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3312_, lean_object* v_i_3313_, lean_object* v_bs_3314_){
_start:
{
size_t v_sz_boxed_3315_; size_t v_i_boxed_3316_; lean_object* v_res_3317_; 
v_sz_boxed_3315_ = lean_unbox_usize(v_sz_3312_);
lean_dec(v_sz_3312_);
v_i_boxed_3316_ = lean_unbox_usize(v_i_3313_);
lean_dec(v_i_3313_);
v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3315_, v_i_boxed_3316_, v_bs_3314_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3318_){
_start:
{
size_t v_sz_3319_; size_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_sz_3319_ = lean_array_size(v_a_3318_);
v___x_3320_ = ((size_t)0ULL);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3319_, v___x_3320_, v_a_3318_);
v___x_3322_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
if (lean_obj_tag(v_a_3323_) == 0)
{
lean_object* v___x_3325_; 
v___x_3325_ = l_List_reverse___redArg(v_a_3324_);
return v___x_3325_;
}
else
{
lean_object* v_head_3326_; lean_object* v_snd_3327_; lean_object* v_tail_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3397_; 
v_head_3326_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_head_3326_);
v_snd_3327_ = lean_ctor_get(v_head_3326_, 1);
lean_inc(v_snd_3327_);
v_tail_3328_ = lean_ctor_get(v_a_3323_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3323_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_a_3323_, 0);
lean_dec(v_unused_3398_);
v___x_3330_ = v_a_3323_;
v_isShared_3331_ = v_isSharedCheck_3397_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_tail_3328_);
lean_dec(v_a_3323_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3397_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_fst_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3395_; 
v_fst_3332_ = lean_ctor_get(v_head_3326_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_head_3326_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v_head_3326_, 1);
lean_dec(v_unused_3396_);
v___x_3334_ = v_head_3326_;
v_isShared_3335_ = v_isSharedCheck_3395_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_fst_3332_);
lean_dec(v_head_3326_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3395_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v_definition_x3f_3336_; lean_object* v_usages_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3394_; 
v_definition_x3f_3336_ = lean_ctor_get(v_snd_3327_, 0);
v_usages_3337_ = lean_ctor_get(v_snd_3327_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_snd_3327_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3339_ = v_snd_3327_;
v_isShared_3340_ = v_isSharedCheck_3394_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_usages_3337_);
lean_inc(v_definition_x3f_3336_);
lean_dec(v_snd_3327_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3394_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___y_3345_; lean_object* v___y_3368_; 
v___x_3341_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3332_);
v___x_3342_ = l_Lean_Json_compress(v___x_3341_);
v___x_3343_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3336_) == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_box(0);
v___y_3345_ = v___x_3370_;
goto v___jp_3344_;
}
else
{
lean_object* v_val_3371_; lean_object* v_startPosLine_3372_; lean_object* v_startPosCharacter_3373_; lean_object* v_endPosLine_3374_; lean_object* v_endPosCharacter_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v_range_3381_; lean_object* v___x_3382_; 
v_val_3371_ = lean_ctor_get(v_definition_x3f_3336_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v_definition_x3f_3336_, 1);
v_startPosLine_3372_ = lean_ctor_get(v_val_3371_, 0);
v_startPosCharacter_3373_ = lean_ctor_get(v_val_3371_, 1);
v_endPosLine_3374_ = lean_ctor_get(v_val_3371_, 2);
v_endPosCharacter_3375_ = lean_ctor_get(v_val_3371_, 3);
v___x_3376_ = lean_box(0);
lean_inc(v_endPosCharacter_3375_);
v___x_3377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3377_, 0, v_endPosCharacter_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
lean_inc(v_endPosLine_3374_);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_endPosLine_3374_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
lean_inc(v_startPosCharacter_3373_);
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_startPosCharacter_3373_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
lean_inc(v_startPosLine_3372_);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_startPosLine_3372_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v_range_3381_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3380_, v___x_3376_);
v___x_3382_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3371_);
lean_dec(v_val_3371_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3383_; 
v___x_3383_ = l_List_appendTR___redArg(v_range_3381_, v___x_3376_);
v___y_3368_ = v___x_3383_;
goto v___jp_3367_;
}
else
{
lean_object* v_val_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3393_; 
v_val_3384_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3386_ = v___x_3382_;
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_val_3384_);
lean_dec(v___x_3382_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3393_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 3);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_val_3384_);
v___x_3389_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3376_);
v___x_3391_ = l_List_appendTR___redArg(v_range_3381_, v___x_3390_);
v___y_3368_ = v___x_3391_;
goto v___jp_3367_;
}
}
}
}
v___jp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3345_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 1, v___x_3346_);
lean_ctor_set(v___x_3334_, 0, v___x_3343_);
v___x_3348_ = v___x_3334_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; size_t v_sz_3350_; size_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3349_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3350_ = lean_array_size(v_usages_3337_);
v___x_3351_ = ((size_t)0ULL);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3350_, v___x_3351_, v_usages_3337_);
v___x_3353_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3352_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v___x_3353_);
lean_ctor_set(v___x_3339_, 0, v___x_3349_);
v___x_3355_ = v___x_3339_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3356_);
lean_ctor_set(v___x_3330_, 0, v___x_3355_);
v___x_3358_ = v___x_3330_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3348_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_Json_mkObj(v___x_3359_);
lean_dec_ref_known(v___x_3359_, 2);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3342_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v_a_3324_);
v_a_3323_ = v_tail_3328_;
v_a_3324_ = v___x_3362_;
goto _start;
}
}
}
}
v___jp_3367_:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___y_3368_);
v___y_3345_ = v___x_3369_;
goto v___jp_3344_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
if (lean_obj_tag(v_a_3399_) == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = l_List_reverse___redArg(v_a_3400_);
return v___x_3401_;
}
else
{
lean_object* v_head_3402_; lean_object* v_snd_3403_; lean_object* v_tail_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3456_; 
v_head_3402_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_head_3402_);
v_snd_3403_ = lean_ctor_get(v_head_3402_, 1);
lean_inc(v_snd_3403_);
v_tail_3404_ = lean_ctor_get(v_a_3399_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_a_3399_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v_a_3399_, 0);
lean_dec(v_unused_3457_);
v___x_3406_ = v_a_3399_;
v_isShared_3407_ = v_isSharedCheck_3456_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_tail_3404_);
lean_dec(v_a_3399_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3456_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v_fst_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3454_; 
v_fst_3408_ = lean_ctor_get(v_head_3402_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_head_3402_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v_head_3402_, 1);
lean_dec(v_unused_3455_);
v___x_3410_ = v_head_3402_;
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_fst_3408_);
lean_dec(v_head_3402_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_rangeStartPosLine_3412_; lean_object* v_rangeStartPosCharacter_3413_; lean_object* v_rangeEndPosLine_3414_; lean_object* v_rangeEndPosCharacter_3415_; lean_object* v_selectionRangeStartPosLine_3416_; lean_object* v_selectionRangeStartPosCharacter_3417_; lean_object* v_selectionRangeEndPosLine_3418_; lean_object* v_selectionRangeEndPosCharacter_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v_rangeStartPosLine_3412_ = lean_ctor_get(v_snd_3403_, 0);
lean_inc(v_rangeStartPosLine_3412_);
v_rangeStartPosCharacter_3413_ = lean_ctor_get(v_snd_3403_, 1);
lean_inc(v_rangeStartPosCharacter_3413_);
v_rangeEndPosLine_3414_ = lean_ctor_get(v_snd_3403_, 2);
lean_inc(v_rangeEndPosLine_3414_);
v_rangeEndPosCharacter_3415_ = lean_ctor_get(v_snd_3403_, 3);
lean_inc(v_rangeEndPosCharacter_3415_);
v_selectionRangeStartPosLine_3416_ = lean_ctor_get(v_snd_3403_, 4);
lean_inc(v_selectionRangeStartPosLine_3416_);
v_selectionRangeStartPosCharacter_3417_ = lean_ctor_get(v_snd_3403_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3417_);
v_selectionRangeEndPosLine_3418_ = lean_ctor_get(v_snd_3403_, 6);
lean_inc(v_selectionRangeEndPosLine_3418_);
v_selectionRangeEndPosCharacter_3419_ = lean_ctor_get(v_snd_3403_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3419_);
lean_dec(v_snd_3403_);
v___x_3420_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3412_);
v___x_3421_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
v___x_3422_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3413_);
v___x_3423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
v___x_3424_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3414_);
v___x_3425_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
v___x_3426_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3415_);
v___x_3427_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
v___x_3428_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3416_);
v___x_3429_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
v___x_3430_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3417_);
v___x_3431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
v___x_3432_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3418_);
v___x_3433_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
v___x_3434_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3419_);
v___x_3435_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
v___x_3436_ = lean_unsigned_to_nat(8u);
v___x_3437_ = lean_mk_empty_array_with_capacity(v___x_3436_);
v___x_3438_ = lean_array_push(v___x_3437_, v___x_3421_);
v___x_3439_ = lean_array_push(v___x_3438_, v___x_3423_);
v___x_3440_ = lean_array_push(v___x_3439_, v___x_3425_);
v___x_3441_ = lean_array_push(v___x_3440_, v___x_3427_);
v___x_3442_ = lean_array_push(v___x_3441_, v___x_3429_);
v___x_3443_ = lean_array_push(v___x_3442_, v___x_3431_);
v___x_3444_ = lean_array_push(v___x_3443_, v___x_3433_);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3435_);
v___x_3446_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v___x_3446_);
v___x_3448_ = v___x_3410_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3408_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v_a_3400_);
lean_ctor_set(v___x_3406_, 0, v___x_3448_);
v___x_3450_ = v___x_3406_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_a_3400_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
v_a_3399_ = v_tail_3404_;
v_a_3400_ = v___x_3450_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3458_, lean_object* v_x_3459_){
_start:
{
if (lean_obj_tag(v_x_3459_) == 0)
{
lean_object* v_k_3460_; lean_object* v_v_3461_; lean_object* v_l_3462_; lean_object* v_r_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_k_3460_ = lean_ctor_get(v_x_3459_, 1);
v_v_3461_ = lean_ctor_get(v_x_3459_, 2);
v_l_3462_ = lean_ctor_get(v_x_3459_, 3);
v_r_3463_ = lean_ctor_get(v_x_3459_, 4);
v___x_3464_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3458_, v_r_3463_);
lean_inc(v_v_3461_);
lean_inc(v_k_3460_);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v_k_3460_);
lean_ctor_set(v___x_3465_, 1, v_v_3461_);
v___x_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3464_);
v_init_3458_ = v___x_3466_;
v_x_3459_ = v_l_3462_;
goto _start;
}
else
{
return v_init_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3468_, lean_object* v_x_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3468_, v_x_3469_);
lean_dec(v_x_3469_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3471_){
_start:
{
lean_object* v_version_3472_; lean_object* v_references_3473_; lean_object* v_decls_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_version_3472_ = lean_ctor_get(v_x_3471_, 0);
lean_inc(v_version_3472_);
v_references_3473_ = lean_ctor_get(v_x_3471_, 1);
lean_inc(v_references_3473_);
v_decls_3474_ = lean_ctor_get(v_x_3471_, 2);
lean_inc(v_decls_3474_);
lean_dec_ref(v_x_3471_);
v___x_3475_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3476_ = l_Lean_JsonNumber_fromNat(v_version_3472_);
v___x_3477_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_box(0);
v___x_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3482_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3479_, v_references_3473_);
lean_dec(v_references_3473_);
v___x_3483_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3482_, v___x_3479_);
v___x_3484_ = l_Lean_Json_mkObj(v___x_3483_);
lean_dec(v___x_3483_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3481_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___x_3479_);
v___x_3487_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3488_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3479_, v_decls_3474_);
lean_dec(v_decls_3474_);
v___x_3489_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3488_, v___x_3479_);
v___x_3490_ = l_Lean_Json_mkObj(v___x_3489_);
lean_dec(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3487_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
lean_ctor_set(v___x_3492_, 1, v___x_3479_);
v___x_3493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3479_);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3486_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3480_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3497_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3495_, v___x_3496_);
v___x_3498_ = l_Lean_Json_mkObj(v___x_3497_);
lean_dec(v___x_3497_);
return v___x_3498_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3501_, size_t v_i_3502_, lean_object* v_bs_3503_){
_start:
{
uint8_t v___x_3504_; 
v___x_3504_ = lean_usize_dec_lt(v_i_3502_, v_sz_3501_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_bs_3503_);
return v___x_3505_;
}
else
{
lean_object* v_v_3506_; lean_object* v___x_3507_; 
v_v_3506_ = lean_array_uget_borrowed(v_bs_3503_, v_i_3502_);
lean_inc(v_v_3506_);
v___x_3507_ = l_Lean_Json_getStr_x3f(v_v_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_bs_3503_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v_bs_x27_3518_; size_t v___x_3519_; size_t v___x_3520_; lean_object* v___x_3521_; 
v_a_3516_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3517_ = lean_unsigned_to_nat(0u);
v_bs_x27_3518_ = lean_array_uset(v_bs_3503_, v_i_3502_, v___x_3517_);
v___x_3519_ = ((size_t)1ULL);
v___x_3520_ = lean_usize_add(v_i_3502_, v___x_3519_);
v___x_3521_ = lean_array_uset(v_bs_x27_3518_, v_i_3502_, v_a_3516_);
v_i_3502_ = v___x_3520_;
v_bs_3503_ = v___x_3521_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3501_ = stack[0].m_num;
size_t v_i_3502_ = stack[1].m_num;
lean_object* v_bs_3503_ = stack[2].m_obj;
lean_object* v_res_3523_;
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3501_, v_i_3502_, v_bs_3503_);
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3524_, lean_object* v_i_3525_, lean_object* v_bs_3526_){
_start:
{
size_t v_sz_boxed_3527_; size_t v_i_boxed_3528_; lean_object* v_res_3529_; 
v_sz_boxed_3527_ = lean_unbox_usize(v_sz_3524_);
lean_dec(v_sz_3524_);
v_i_boxed_3528_ = lean_unbox_usize(v_i_3525_);
lean_dec(v_i_3525_);
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3527_, v_i_boxed_3528_, v_bs_3526_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3530_){
_start:
{
if (lean_obj_tag(v_x_3530_) == 4)
{
lean_object* v_elems_3531_; size_t v_sz_3532_; size_t v___x_3533_; lean_object* v___x_3534_; 
v_elems_3531_ = lean_ctor_get(v_x_3530_, 0);
lean_inc_ref(v_elems_3531_);
lean_dec_ref_known(v_x_3530_, 1);
v_sz_3532_ = lean_array_size(v_elems_3531_);
v___x_3533_ = ((size_t)0ULL);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3532_, v___x_3533_, v_elems_3531_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3535_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3536_ = lean_unsigned_to_nat(80u);
v___x_3537_ = l_Lean_Json_pretty(v_x_3530_, v___x_3536_);
v___x_3538_ = lean_string_append(v___x_3535_, v___x_3537_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3542_, lean_object* v_k_3543_){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = l_Lean_Json_getObjValD(v_j_3542_, v_k_3543_);
v___x_3545_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3546_, lean_object* v_k_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3546_, v_k_3547_);
lean_dec_ref(v_k_3547_);
return v_res_3548_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = 1;
v___x_3556_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3559_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3560_ = lean_string_append(v___x_3559_, v___x_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = 1;
v___x_3564_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3568_ = lean_string_append(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3570_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3571_ = lean_string_append(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3574_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3572_, v___x_3573_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3584_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3584_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3584_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3579_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3580_ = lean_string_append(v___x_3579_, v_a_3575_);
lean_dec(v_a_3575_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3580_);
v___x_3582_ = v___x_3577_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
else
{
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
v_a_3585_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3574_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3574_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set_tag(v___x_3587_, 0);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
v_a_3593_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3574_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3574_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3603_, size_t v_i_3604_, lean_object* v_bs_3605_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_usize_dec_lt(v_i_3604_, v_sz_3603_);
if (v___x_3606_ == 0)
{
return v_bs_3605_;
}
else
{
lean_object* v_v_3607_; lean_object* v___x_3608_; lean_object* v_bs_x27_3609_; lean_object* v___x_3610_; size_t v___x_3611_; size_t v___x_3612_; lean_object* v___x_3613_; 
v_v_3607_ = lean_array_uget(v_bs_3605_, v_i_3604_);
v___x_3608_ = lean_unsigned_to_nat(0u);
v_bs_x27_3609_ = lean_array_uset(v_bs_3605_, v_i_3604_, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_v_3607_);
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_add(v_i_3604_, v___x_3611_);
v___x_3613_ = lean_array_uset(v_bs_x27_3609_, v_i_3604_, v___x_3610_);
v_i_3604_ = v___x_3612_;
v_bs_3605_ = v___x_3613_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3603_ = stack[0].m_num;
size_t v_i_3604_ = stack[1].m_num;
lean_object* v_bs_3605_ = stack[2].m_obj;
lean_object* v_res_3615_;
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3603_, v_i_3604_, v_bs_3605_);
stack->m_obj
 = v_res_3615_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_bs_3618_){
_start:
{
size_t v_sz_boxed_3619_; size_t v_i_boxed_3620_; lean_object* v_res_3621_; 
v_sz_boxed_3619_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3620_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3619_, v_i_boxed_3620_, v_bs_3618_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3622_){
_start:
{
size_t v_sz_3623_; size_t v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_sz_3623_ = lean_array_size(v_a_3622_);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3623_, v___x_3624_, v_a_3622_);
v___x_3626_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3628_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3629_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3627_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3631_);
v___x_3634_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3635_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3633_, v___x_3634_);
v___x_3636_ = l_Lean_Json_mkObj(v___x_3635_);
lean_dec(v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3639_, lean_object* v_k_3640_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = l_Lean_Json_getObjValD(v_j_3639_, v_k_3640_);
v___x_3642_ = l_Lean_Json_getStr_x3f(v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3643_, lean_object* v_k_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3643_, v_k_3644_);
lean_dec_ref(v_k_3644_);
return v_res_3645_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = 1;
v___x_3653_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3654_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3653_, v___x_3652_);
return v___x_3654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3656_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3657_ = lean_string_append(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = 1;
v___x_3661_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3661_, v___x_3660_);
return v___x_3662_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3664_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3665_ = lean_string_append(v___x_3664_, v___x_3663_);
return v___x_3665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3667_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3668_ = lean_string_append(v___x_3667_, v___x_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3669_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3669_, v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3681_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3677_ = lean_string_append(v___x_3676_, v_a_3672_);
lean_dec(v_a_3672_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3677_);
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
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
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3682_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3671_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3671_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set_tag(v___x_3684_, 0);
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_a_3690_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3671_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3671_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3700_){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3701_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_x_3700_);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = lean_box(0);
v___x_3705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
lean_ctor_set(v___x_3706_, 1, v___x_3704_);
v___x_3707_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3708_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3706_, v___x_3707_);
v___x_3709_ = l_Lean_Json_mkObj(v___x_3708_);
lean_dec(v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl(lean_object* v_x_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_obj_tag_nat(v_x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl___boxed(lean_object* v_x_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Lsp_OpenNamespace_ctorIdx___impl(v_x_3714_);
lean_dec_ref(v_x_3714_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3716_, lean_object* v_k_3717_){
_start:
{
if (lean_obj_tag(v_t_3716_) == 0)
{
lean_object* v_namespace_3718_; lean_object* v_exceptions_3719_; lean_object* v___x_3720_; 
v_namespace_3718_ = lean_ctor_get(v_t_3716_, 0);
lean_inc(v_namespace_3718_);
v_exceptions_3719_ = lean_ctor_get(v_t_3716_, 1);
lean_inc_ref(v_exceptions_3719_);
lean_dec_ref_known(v_t_3716_, 2);
v___x_3720_ = lean_apply_2(v_k_3717_, v_namespace_3718_, v_exceptions_3719_);
return v___x_3720_;
}
else
{
lean_object* v_from_3721_; lean_object* v_to_3722_; lean_object* v___x_3723_; 
v_from_3721_ = lean_ctor_get(v_t_3716_, 0);
lean_inc(v_from_3721_);
v_to_3722_ = lean_ctor_get(v_t_3716_, 1);
lean_inc(v_to_3722_);
lean_dec_ref_known(v_t_3716_, 2);
v___x_3723_ = lean_apply_2(v_k_3717_, v_from_3721_, v_to_3722_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3724_, lean_object* v_ctorIdx_3725_, lean_object* v_t_3726_, lean_object* v_h_3727_, lean_object* v_k_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3726_, v_k_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3730_, lean_object* v_ctorIdx_3731_, lean_object* v_t_3732_, lean_object* v_h_3733_, lean_object* v_k_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3730_, v_ctorIdx_3731_, v_t_3732_, v_h_3733_, v_k_3734_);
lean_dec(v_ctorIdx_3731_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3736_, lean_object* v_allExcept_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3736_, v_allExcept_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3739_, lean_object* v_t_3740_, lean_object* v_h_3741_, lean_object* v_allExcept_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3740_, v_allExcept_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3744_, lean_object* v_renamed_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3744_, v_renamed_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3747_, lean_object* v_t_3748_, lean_object* v_h_3749_, lean_object* v_renamed_3750_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3748_, v_renamed_3750_);
return v___x_3751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3752_, size_t v_i_3753_, lean_object* v_bs_3754_){
_start:
{
uint8_t v___x_3755_; 
v___x_3755_ = lean_usize_dec_lt(v_i_3753_, v_sz_3752_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_bs_3754_);
return v___x_3756_;
}
else
{
lean_object* v_v_3757_; lean_object* v___x_3758_; 
v_v_3757_ = lean_array_uget_borrowed(v_bs_3754_, v_i_3753_);
lean_inc(v_v_3757_);
v___x_3758_ = l_Lean_Name_fromJson_x3f(v_v_3757_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v_bs_3754_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
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
lean_object* v_a_3767_; lean_object* v___x_3768_; lean_object* v_bs_x27_3769_; size_t v___x_3770_; size_t v___x_3771_; lean_object* v___x_3772_; 
v_a_3767_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3768_ = lean_unsigned_to_nat(0u);
v_bs_x27_3769_ = lean_array_uset(v_bs_3754_, v_i_3753_, v___x_3768_);
v___x_3770_ = ((size_t)1ULL);
v___x_3771_ = lean_usize_add(v_i_3753_, v___x_3770_);
v___x_3772_ = lean_array_uset(v_bs_x27_3769_, v_i_3753_, v_a_3767_);
v_i_3753_ = v___x_3771_;
v_bs_3754_ = v___x_3772_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3752_ = stack[0].m_num;
size_t v_i_3753_ = stack[1].m_num;
lean_object* v_bs_3754_ = stack[2].m_obj;
lean_object* v_res_3774_;
v_res_3774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3752_, v_i_3753_, v_bs_3754_);
stack->m_obj
 = v_res_3774_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3775_, lean_object* v_i_3776_, lean_object* v_bs_3777_){
_start:
{
size_t v_sz_boxed_3778_; size_t v_i_boxed_3779_; lean_object* v_res_3780_; 
v_sz_boxed_3778_ = lean_unbox_usize(v_sz_3775_);
lean_dec(v_sz_3775_);
v_i_boxed_3779_ = lean_unbox_usize(v_i_3776_);
lean_dec(v_i_3776_);
v_res_3780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3778_, v_i_boxed_3779_, v_bs_3777_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3781_){
_start:
{
if (lean_obj_tag(v_x_3781_) == 4)
{
lean_object* v_elems_3782_; size_t v_sz_3783_; size_t v___x_3784_; lean_object* v___x_3785_; 
v_elems_3782_ = lean_ctor_get(v_x_3781_, 0);
lean_inc_ref(v_elems_3782_);
lean_dec_ref_known(v_x_3781_, 1);
v_sz_3783_ = lean_array_size(v_elems_3782_);
v___x_3784_ = ((size_t)0ULL);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3783_, v___x_3784_, v_elems_3782_);
return v___x_3785_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3786_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3787_ = lean_unsigned_to_nat(80u);
v___x_3788_ = l_Lean_Json_pretty(v_x_3781_, v___x_3787_);
v___x_3789_ = lean_string_append(v___x_3786_, v___x_3788_);
lean_dec_ref(v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3791_ = lean_string_append(v___x_3789_, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3827_){
_start:
{
lean_object* v___x_3828_; 
lean_inc(v_json_3827_);
v___x_3828_ = l_Lean_Json_getTag_x3f(v_json_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
lean_dec(v_json_3827_);
v___x_3829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3829_;
}
else
{
lean_object* v_val_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_val_3830_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_val_3830_);
lean_dec_ref_known(v___x_3828_, 1);
v___x_3831_ = lean_box(0);
v___x_3832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3833_ = lean_string_dec_eq(v_val_3830_, v___x_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; uint8_t v___x_3835_; 
v___x_3834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3835_ = lean_string_dec_eq(v_val_3830_, v___x_3834_);
lean_dec(v_val_3830_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_dec(v_json_3827_);
v___x_3836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3836_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = lean_unsigned_to_nat(2u);
v___x_3838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3839_ = l_Lean_Json_parseCtorFields(v_json_3827_, v___x_3834_, v___x_3837_, v___x_3838_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_a_3848_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3849_ = lean_unsigned_to_nat(0u);
v___x_3850_ = lean_array_get_borrowed(v___x_3831_, v_a_3848_, v___x_3849_);
lean_inc(v___x_3850_);
v___x_3851_ = l_Lean_Name_fromJson_x3f(v___x_3850_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_a_3848_);
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3860_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3851_, 1);
v___x_3861_ = lean_unsigned_to_nat(1u);
v___x_3862_ = lean_array_get(v___x_3831_, v_a_3848_, v___x_3861_);
lean_dec(v_a_3848_);
v___x_3863_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3862_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_a_3860_);
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3880_; 
v_a_3872_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3874_ = v___x_3863_;
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3863_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_a_3860_);
lean_ctor_set(v___x_3876_, 1, v_a_3872_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3876_);
v___x_3878_ = v___x_3874_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec(v_val_3830_);
v___x_3881_ = lean_unsigned_to_nat(2u);
v___x_3882_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3883_ = l_Lean_Json_parseCtorFields(v_json_3827_, v___x_3832_, v___x_3881_, v___x_3882_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
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
lean_object* v_a_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_a_3892_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_array_get_borrowed(v___x_3831_, v_a_3892_, v___x_3893_);
lean_inc(v___x_3894_);
v___x_3895_ = l_Lean_Name_fromJson_x3f(v___x_3894_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v_a_3892_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3904_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = lean_array_get(v___x_3831_, v_a_3892_, v___x_3905_);
lean_dec(v_a_3892_);
v___x_3907_ = l_Lean_Name_fromJson_x3f(v___x_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec(v_a_3904_);
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
v_a_3916_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v___x_3907_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3907_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3920_, 0, v_a_3904_);
lean_ctor_set(v___x_3920_, 1, v_a_3916_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3927_, size_t v_i_3928_, lean_object* v_bs_3929_){
_start:
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_usize_dec_lt(v_i_3928_, v_sz_3927_);
if (v___x_3930_ == 0)
{
return v_bs_3929_;
}
else
{
lean_object* v_v_3931_; lean_object* v___x_3932_; lean_object* v_bs_x27_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v___x_3938_; 
v_v_3931_ = lean_array_uget(v_bs_3929_, v_i_3928_);
v___x_3932_ = lean_unsigned_to_nat(0u);
v_bs_x27_3933_ = lean_array_uset(v_bs_3929_, v_i_3928_, v___x_3932_);
v___x_3934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3931_, v___x_3930_);
v___x_3935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
v___x_3936_ = ((size_t)1ULL);
v___x_3937_ = lean_usize_add(v_i_3928_, v___x_3936_);
v___x_3938_ = lean_array_uset(v_bs_x27_3933_, v_i_3928_, v___x_3935_);
v_i_3928_ = v___x_3937_;
v_bs_3929_ = v___x_3938_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3927_ = stack[0].m_num;
size_t v_i_3928_ = stack[1].m_num;
lean_object* v_bs_3929_ = stack[2].m_obj;
lean_object* v_res_3940_;
v_res_3940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3927_, v_i_3928_, v_bs_3929_);
stack->m_obj
 = v_res_3940_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3941_, lean_object* v_i_3942_, lean_object* v_bs_3943_){
_start:
{
size_t v_sz_boxed_3944_; size_t v_i_boxed_3945_; lean_object* v_res_3946_; 
v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3941_);
lean_dec(v_sz_3941_);
v_i_boxed_3945_ = lean_unbox_usize(v_i_3942_);
lean_dec(v_i_3942_);
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3944_, v_i_boxed_3945_, v_bs_3943_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3947_){
_start:
{
size_t v_sz_3948_; size_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_sz_3948_ = lean_array_size(v_a_3947_);
v___x_3949_ = ((size_t)0ULL);
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3948_, v___x_3949_, v_a_3947_);
v___x_3951_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3952_){
_start:
{
if (lean_obj_tag(v_x_3952_) == 0)
{
lean_object* v_namespace_3953_; lean_object* v_exceptions_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3976_; 
v_namespace_3953_ = lean_ctor_get(v_x_3952_, 0);
v_exceptions_3954_ = lean_ctor_get(v_x_3952_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_x_3952_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3956_ = v_x_3952_;
v_isShared_3957_ = v_isSharedCheck_3976_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_exceptions_3954_);
lean_inc(v_namespace_3953_);
lean_dec(v_x_3952_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3976_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3960_ = 1;
v___x_3961_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3953_, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3962_);
lean_ctor_set(v___x_3956_, 0, v___x_3959_);
v___x_3964_ = v___x_3956_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3965_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3966_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3954_);
v___x_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3964_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l_Lean_Json_mkObj(v___x_3970_);
lean_dec_ref_known(v___x_3970_, 2);
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3958_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v___x_3968_);
v___x_3974_ = l_Lean_Json_mkObj(v___x_3973_);
lean_dec_ref_known(v___x_3973_, 2);
return v___x_3974_;
}
}
}
else
{
lean_object* v_from_3977_; lean_object* v_to_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4001_; 
v_from_3977_ = lean_ctor_get(v_x_3952_, 0);
v_to_3978_ = lean_ctor_get(v_x_3952_, 1);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_x_3952_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3980_ = v_x_3952_;
v_isShared_3981_ = v_isSharedCheck_4001_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_to_3978_);
lean_inc(v_from_3977_);
lean_dec(v_x_3952_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4001_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3982_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3983_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3984_ = 1;
v___x_3985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3977_, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set_tag(v___x_3980_, 0);
lean_ctor_set(v___x_3980_, 1, v___x_3986_);
lean_ctor_set(v___x_3980_, 0, v___x_3983_);
v___x_3988_ = v___x_3980_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3989_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3978_, v___x_3984_);
v___x_3991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3989_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_box(0);
v___x_3994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3988_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_Json_mkObj(v___x_3995_);
lean_dec_ref_known(v___x_3995_, 2);
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3982_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___x_3993_);
v___x_3999_ = l_Lean_Json_mkObj(v___x_3998_);
lean_dec_ref_known(v___x_3998_, 2);
return v___x_3999_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4004_, size_t v_i_4005_, lean_object* v_bs_4006_){
_start:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_usize_dec_lt(v_i_4005_, v_sz_4004_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4008_, 0, v_bs_4006_);
return v___x_4008_;
}
else
{
lean_object* v_v_4009_; lean_object* v___x_4010_; 
v_v_4009_ = lean_array_uget_borrowed(v_bs_4006_, v_i_4005_);
lean_inc(v_v_4009_);
v___x_4010_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_4009_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v_bs_4006_);
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4020_; lean_object* v_bs_x27_4021_; size_t v___x_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v_a_4019_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4020_ = lean_unsigned_to_nat(0u);
v_bs_x27_4021_ = lean_array_uset(v_bs_4006_, v_i_4005_, v___x_4020_);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_add(v_i_4005_, v___x_4022_);
v___x_4024_ = lean_array_uset(v_bs_x27_4021_, v_i_4005_, v_a_4019_);
v_i_4005_ = v___x_4023_;
v_bs_4006_ = v___x_4024_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4004_ = stack[0].m_num;
size_t v_i_4005_ = stack[1].m_num;
lean_object* v_bs_4006_ = stack[2].m_obj;
lean_object* v_res_4026_;
v_res_4026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4004_, v_i_4005_, v_bs_4006_);
stack->m_obj
 = v_res_4026_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4027_, lean_object* v_i_4028_, lean_object* v_bs_4029_){
_start:
{
size_t v_sz_boxed_4030_; size_t v_i_boxed_4031_; lean_object* v_res_4032_; 
v_sz_boxed_4030_ = lean_unbox_usize(v_sz_4027_);
lean_dec(v_sz_4027_);
v_i_boxed_4031_ = lean_unbox_usize(v_i_4028_);
lean_dec(v_i_4028_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4030_, v_i_boxed_4031_, v_bs_4029_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4033_){
_start:
{
if (lean_obj_tag(v_x_4033_) == 4)
{
lean_object* v_elems_4034_; size_t v_sz_4035_; size_t v___x_4036_; lean_object* v___x_4037_; 
v_elems_4034_ = lean_ctor_get(v_x_4033_, 0);
lean_inc_ref(v_elems_4034_);
lean_dec_ref_known(v_x_4033_, 1);
v_sz_4035_ = lean_array_size(v_elems_4034_);
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4035_, v___x_4036_, v_elems_4034_);
return v___x_4037_;
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4038_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4039_ = lean_unsigned_to_nat(80u);
v___x_4040_ = l_Lean_Json_pretty(v_x_4033_, v___x_4039_);
v___x_4041_ = lean_string_append(v___x_4038_, v___x_4040_);
lean_dec_ref(v___x_4040_);
v___x_4042_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4043_ = lean_string_append(v___x_4041_, v___x_4042_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4045_, lean_object* v_k_4046_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = l_Lean_Json_getObjValD(v_j_4045_, v_k_4046_);
v___x_4048_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4049_, lean_object* v_k_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4049_, v_k_4050_);
lean_dec_ref(v_k_4050_);
return v_res_4051_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = 1;
v___x_4059_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4059_, v___x_4058_);
return v___x_4060_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4062_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4063_ = lean_string_append(v___x_4062_, v___x_4061_);
return v___x_4063_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = 1;
v___x_4067_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4067_, v___x_4066_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4070_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4071_ = lean_string_append(v___x_4070_, v___x_4069_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4073_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4074_ = lean_string_append(v___x_4073_, v___x_4072_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = 1;
v___x_4079_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4080_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4079_, v___x_4078_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4082_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4083_ = lean_string_append(v___x_4082_, v___x_4081_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4085_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4086_ = lean_string_append(v___x_4085_, v___x_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4087_);
v___x_4089_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4087_, v___x_4088_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_json_4087_);
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4097_; 
v___x_4094_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4095_ = lean_string_append(v___x_4094_, v_a_4090_);
lean_dec(v_a_4090_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4095_);
v___x_4097_ = v___x_4092_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
else
{
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_json_4087_);
v_a_4100_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4089_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4089_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set_tag(v___x_4102_, 0);
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
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
lean_object* v_a_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v_a_4108_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4110_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4087_, v___x_4109_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_a_4108_);
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4120_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4120_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4116_ = lean_string_append(v___x_4115_, v_a_4111_);
lean_dec(v_a_4111_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4116_);
v___x_4118_ = v___x_4113_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
else
{
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
lean_dec(v_a_4108_);
v_a_4121_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4110_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4110_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set_tag(v___x_4123_, 0);
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4137_; 
v_a_4129_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4131_ = v___x_4110_;
v_isShared_4132_ = v_isSharedCheck_4137_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4110_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4137_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4133_, 0, v_a_4108_);
lean_ctor_set(v___x_4133_, 1, v_a_4129_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v___x_4133_);
v___x_4135_ = v___x_4131_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4140_, size_t v_i_4141_, lean_object* v_bs_4142_){
_start:
{
uint8_t v___x_4143_; 
v___x_4143_ = lean_usize_dec_lt(v_i_4141_, v_sz_4140_);
if (v___x_4143_ == 0)
{
return v_bs_4142_;
}
else
{
lean_object* v_v_4144_; lean_object* v___x_4145_; lean_object* v_bs_x27_4146_; lean_object* v___x_4147_; size_t v___x_4148_; size_t v___x_4149_; lean_object* v___x_4150_; 
v_v_4144_ = lean_array_uget(v_bs_4142_, v_i_4141_);
v___x_4145_ = lean_unsigned_to_nat(0u);
v_bs_x27_4146_ = lean_array_uset(v_bs_4142_, v_i_4141_, v___x_4145_);
v___x_4147_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4144_);
v___x_4148_ = ((size_t)1ULL);
v___x_4149_ = lean_usize_add(v_i_4141_, v___x_4148_);
v___x_4150_ = lean_array_uset(v_bs_x27_4146_, v_i_4141_, v___x_4147_);
v_i_4141_ = v___x_4149_;
v_bs_4142_ = v___x_4150_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4140_ = stack[0].m_num;
size_t v_i_4141_ = stack[1].m_num;
lean_object* v_bs_4142_ = stack[2].m_obj;
lean_object* v_res_4152_;
v_res_4152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4140_, v_i_4141_, v_bs_4142_);
stack->m_obj
 = v_res_4152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4153_, lean_object* v_i_4154_, lean_object* v_bs_4155_){
_start:
{
size_t v_sz_boxed_4156_; size_t v_i_boxed_4157_; lean_object* v_res_4158_; 
v_sz_boxed_4156_ = lean_unbox_usize(v_sz_4153_);
lean_dec(v_sz_4153_);
v_i_boxed_4157_ = lean_unbox_usize(v_i_4154_);
lean_dec(v_i_4154_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4156_, v_i_boxed_4157_, v_bs_4155_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4159_){
_start:
{
size_t v_sz_4160_; size_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_sz_4160_ = lean_array_size(v_a_4159_);
v___x_4161_ = ((size_t)0ULL);
v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4160_, v___x_4161_, v_a_4159_);
v___x_4163_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4164_){
_start:
{
lean_object* v_identifier_4165_; lean_object* v_openNamespaces_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4186_; 
v_identifier_4165_ = lean_ctor_get(v_x_4164_, 0);
v_openNamespaces_4166_ = lean_ctor_get(v_x_4164_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_x_4164_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4168_ = v_x_4164_;
v_isShared_4169_ = v_isSharedCheck_4186_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_openNamespaces_4166_);
lean_inc(v_identifier_4165_);
lean_dec(v_x_4164_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4186_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4171_, 0, v_identifier_4165_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v___x_4171_);
lean_ctor_set(v___x_4168_, 0, v___x_4170_);
v___x_4173_ = v___x_4168_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4174_ = lean_box(0);
v___x_4175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
v___x_4176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4177_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4166_);
v___x_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4176_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
v___x_4179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
lean_ctor_set(v___x_4179_, 1, v___x_4174_);
v___x_4180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4174_);
v___x_4181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4175_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4183_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4181_, v___x_4182_);
v___x_4184_ = l_Lean_Json_mkObj(v___x_4183_);
lean_dec(v___x_4183_);
return v___x_4184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4192_, lean_object* v_k_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_Json_getObjValD(v_j_4192_, v_k_4193_);
switch(lean_obj_tag(v___x_4194_))
{
case 3:
{
lean_object* v_s_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4203_; 
v_s_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_s_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set_tag(v___x_4197_, 0);
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_s_4195_);
v___x_4200_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
return v___x_4201_;
}
}
}
case 2:
{
lean_object* v_n_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_n_4204_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v___x_4194_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_n_4204_);
lean_dec(v___x_4194_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 1);
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_n_4204_);
v___x_4209_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
}
default: 
{
lean_object* v___x_4213_; 
lean_dec(v___x_4194_);
v___x_4213_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4214_, lean_object* v_k_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4214_, v_k_4215_);
lean_dec_ref(v_k_4215_);
return v_res_4216_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4217_, size_t v_i_4218_, lean_object* v_bs_4219_){
_start:
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_usize_dec_lt(v_i_4218_, v_sz_4217_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_bs_4219_);
return v___x_4221_;
}
else
{
lean_object* v_v_4222_; lean_object* v___x_4223_; 
v_v_4222_ = lean_array_uget_borrowed(v_bs_4219_, v_i_4218_);
lean_inc(v_v_4222_);
v___x_4223_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4222_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v_bs_4219_);
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4223_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v_bs_x27_4234_; size_t v___x_4235_; size_t v___x_4236_; lean_object* v___x_4237_; 
v_a_4232_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4223_, 1);
v___x_4233_ = lean_unsigned_to_nat(0u);
v_bs_x27_4234_ = lean_array_uset(v_bs_4219_, v_i_4218_, v___x_4233_);
v___x_4235_ = ((size_t)1ULL);
v___x_4236_ = lean_usize_add(v_i_4218_, v___x_4235_);
v___x_4237_ = lean_array_uset(v_bs_x27_4234_, v_i_4218_, v_a_4232_);
v_i_4218_ = v___x_4236_;
v_bs_4219_ = v___x_4237_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4217_ = stack[0].m_num;
size_t v_i_4218_ = stack[1].m_num;
lean_object* v_bs_4219_ = stack[2].m_obj;
lean_object* v_res_4239_;
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4217_, v_i_4218_, v_bs_4219_);
stack->m_obj
 = v_res_4239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4240_, lean_object* v_i_4241_, lean_object* v_bs_4242_){
_start:
{
size_t v_sz_boxed_4243_; size_t v_i_boxed_4244_; lean_object* v_res_4245_; 
v_sz_boxed_4243_ = lean_unbox_usize(v_sz_4240_);
lean_dec(v_sz_4240_);
v_i_boxed_4244_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4243_, v_i_boxed_4244_, v_bs_4242_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4246_){
_start:
{
if (lean_obj_tag(v_x_4246_) == 4)
{
lean_object* v_elems_4247_; size_t v_sz_4248_; size_t v___x_4249_; lean_object* v___x_4250_; 
v_elems_4247_ = lean_ctor_get(v_x_4246_, 0);
lean_inc_ref(v_elems_4247_);
lean_dec_ref_known(v_x_4246_, 1);
v_sz_4248_ = lean_array_size(v_elems_4247_);
v___x_4249_ = ((size_t)0ULL);
v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4248_, v___x_4249_, v_elems_4247_);
return v___x_4250_;
}
else
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4251_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4252_ = lean_unsigned_to_nat(80u);
v___x_4253_ = l_Lean_Json_pretty(v_x_4246_, v___x_4252_);
v___x_4254_ = lean_string_append(v___x_4251_, v___x_4253_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4256_ = lean_string_append(v___x_4254_, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4258_, lean_object* v_k_4259_){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = l_Lean_Json_getObjValD(v_j_4258_, v_k_4259_);
v___x_4261_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4262_, lean_object* v_k_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4262_, v_k_4263_);
lean_dec_ref(v_k_4263_);
return v_res_4264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = 1;
v___x_4272_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4273_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4272_, v___x_4271_);
return v___x_4273_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4275_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4276_ = lean_string_append(v___x_4275_, v___x_4274_);
return v___x_4276_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = 1;
v___x_4280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4280_, v___x_4279_);
return v___x_4281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4284_ = lean_string_append(v___x_4283_, v___x_4282_);
return v___x_4284_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4286_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4287_ = lean_string_append(v___x_4286_, v___x_4285_);
return v___x_4287_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = 1;
v___x_4292_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4292_, v___x_4291_);
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4296_ = lean_string_append(v___x_4295_, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4299_ = lean_string_append(v___x_4298_, v___x_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4300_){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4300_);
v___x_4302_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4300_, v___x_4301_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v_json_4300_);
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4312_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4312_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v___x_4307_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4308_ = lean_string_append(v___x_4307_, v_a_4303_);
lean_dec(v_a_4303_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4308_);
v___x_4310_ = v___x_4305_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
else
{
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v_json_4300_);
v_a_4313_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4302_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4302_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set_tag(v___x_4315_, 0);
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4321_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4322_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4323_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4300_, v___x_4322_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v_a_4321_);
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4333_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4333_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4331_; 
v___x_4328_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4329_ = lean_string_append(v___x_4328_, v_a_4324_);
lean_dec(v_a_4324_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4329_);
v___x_4331_ = v___x_4326_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4321_);
v_a_4334_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4323_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4323_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
lean_ctor_set_tag(v___x_4336_, 0);
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4350_; 
v_a_4342_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4344_ = v___x_4323_;
v_isShared_4345_ = v_isSharedCheck_4350_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4323_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4350_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4346_, 0, v_a_4321_);
lean_ctor_set(v___x_4346_, 1, v_a_4342_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4346_);
v___x_4348_ = v___x_4344_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4353_, size_t v_i_4354_, lean_object* v_bs_4355_){
_start:
{
uint8_t v___x_4356_; 
v___x_4356_ = lean_usize_dec_lt(v_i_4354_, v_sz_4353_);
if (v___x_4356_ == 0)
{
return v_bs_4355_;
}
else
{
lean_object* v_v_4357_; lean_object* v___x_4358_; lean_object* v_bs_x27_4359_; lean_object* v___x_4360_; size_t v___x_4361_; size_t v___x_4362_; lean_object* v___x_4363_; 
v_v_4357_ = lean_array_uget(v_bs_4355_, v_i_4354_);
v___x_4358_ = lean_unsigned_to_nat(0u);
v_bs_x27_4359_ = lean_array_uset(v_bs_4355_, v_i_4354_, v___x_4358_);
v___x_4360_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4357_);
v___x_4361_ = ((size_t)1ULL);
v___x_4362_ = lean_usize_add(v_i_4354_, v___x_4361_);
v___x_4363_ = lean_array_uset(v_bs_x27_4359_, v_i_4354_, v___x_4360_);
v_i_4354_ = v___x_4362_;
v_bs_4355_ = v___x_4363_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4353_ = stack[0].m_num;
size_t v_i_4354_ = stack[1].m_num;
lean_object* v_bs_4355_ = stack[2].m_obj;
lean_object* v_res_4365_;
v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4353_, v_i_4354_, v_bs_4355_);
stack->m_obj
 = v_res_4365_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4366_, lean_object* v_i_4367_, lean_object* v_bs_4368_){
_start:
{
size_t v_sz_boxed_4369_; size_t v_i_boxed_4370_; lean_object* v_res_4371_; 
v_sz_boxed_4369_ = lean_unbox_usize(v_sz_4366_);
lean_dec(v_sz_4366_);
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_res_4371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4369_, v_i_boxed_4370_, v_bs_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4372_){
_start:
{
size_t v_sz_4373_; size_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_sz_4373_ = lean_array_size(v_a_4372_);
v___x_4374_ = ((size_t)0ULL);
v___x_4375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4373_, v___x_4374_, v_a_4372_);
v___x_4376_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4377_){
_start:
{
lean_object* v_sourceRequestID_4378_; lean_object* v_queries_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4417_; 
v_sourceRequestID_4378_ = lean_ctor_get(v_x_4377_, 0);
v_queries_4379_ = lean_ctor_get(v_x_4377_, 1);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_x_4377_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4381_ = v_x_4377_;
v_isShared_4382_ = v_isSharedCheck_4417_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_queries_4379_);
lean_inc(v_sourceRequestID_4378_);
lean_dec(v_x_4377_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4417_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___y_4385_; 
v___x_4383_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4378_))
{
case 0:
{
lean_object* v_s_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
v_s_4400_ = lean_ctor_get(v_sourceRequestID_4378_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_sourceRequestID_4378_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v_sourceRequestID_4378_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_s_4400_);
lean_dec(v_sourceRequestID_4378_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set_tag(v___x_4402_, 3);
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_s_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
v___y_4385_ = v___x_4405_;
goto v___jp_4384_;
}
}
}
case 1:
{
lean_object* v_n_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
v_n_4408_ = lean_ctor_get(v_sourceRequestID_4378_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_sourceRequestID_4378_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v_sourceRequestID_4378_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_n_4408_);
lean_dec(v_sourceRequestID_4378_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
lean_ctor_set_tag(v___x_4410_, 2);
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_n_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
v___y_4385_ = v___x_4413_;
goto v___jp_4384_;
}
}
}
default: 
{
lean_object* v___x_4416_; 
v___x_4416_ = lean_box(0);
v___y_4385_ = v___x_4416_;
goto v___jp_4384_;
}
}
v___jp_4384_:
{
lean_object* v___x_4387_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 1, v___y_4385_);
lean_ctor_set(v___x_4381_, 0, v___x_4383_);
v___x_4387_ = v___x_4381_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4399_, 1, v___y_4385_);
v___x_4387_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4388_ = lean_box(0);
v___x_4389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4391_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4379_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
lean_ctor_set(v___x_4393_, 1, v___x_4388_);
v___x_4394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
lean_ctor_set(v___x_4394_, 1, v___x_4388_);
v___x_4395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4389_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4397_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4395_, v___x_4396_);
v___x_4398_ = l_Lean_Json_mkObj(v___x_4397_);
lean_dec(v___x_4397_);
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4420_, lean_object* v_k_4421_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = l_Lean_Json_getObjValD(v_j_4420_, v_k_4421_);
v___x_4423_ = l_Lean_Name_fromJson_x3f(v___x_4422_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4424_, lean_object* v_k_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4424_, v_k_4425_);
lean_dec_ref(v_k_4425_);
return v_res_4426_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4433_ = 1;
v___x_4434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4435_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4434_, v___x_4433_);
return v___x_4435_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4436_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4438_ = lean_string_append(v___x_4437_, v___x_4436_);
return v___x_4438_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4441_ = 1;
v___x_4442_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4443_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4442_, v___x_4441_);
return v___x_4443_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4445_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4446_ = lean_string_append(v___x_4445_, v___x_4444_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4448_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4449_ = lean_string_append(v___x_4448_, v___x_4447_);
return v___x_4449_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4453_ = 1;
v___x_4454_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4454_, v___x_4453_);
return v___x_4455_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4457_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4458_ = lean_string_append(v___x_4457_, v___x_4456_);
return v___x_4458_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4460_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4461_ = lean_string_append(v___x_4460_, v___x_4459_);
return v___x_4461_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4465_ = 1;
v___x_4466_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4466_, v___x_4465_);
return v___x_4467_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4468_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4470_ = lean_string_append(v___x_4469_, v___x_4468_);
return v___x_4470_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4472_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4473_ = lean_string_append(v___x_4472_, v___x_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4474_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4474_);
v___x_4476_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4474_, v___x_4475_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4486_; 
lean_dec(v_json_4474_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4486_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4486_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
v___x_4481_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4482_ = lean_string_append(v___x_4481_, v_a_4477_);
lean_dec(v_a_4477_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4482_);
v___x_4484_ = v___x_4479_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
else
{
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec(v_json_4474_);
v_a_4487_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4476_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4476_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
lean_ctor_set_tag(v___x_4489_, 0);
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
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
lean_object* v_a_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_a_4495_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4476_, 1);
v___x_4496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4474_);
v___x_4497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4474_, v___x_4496_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_a_4495_);
lean_dec(v_json_4474_);
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4500_ = v___x_4497_;
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4497_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4502_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4503_ = lean_string_append(v___x_4502_, v_a_4498_);
lean_dec(v_a_4498_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4503_);
v___x_4505_ = v___x_4500_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
else
{
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4495_);
lean_dec(v_json_4474_);
v_a_4508_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4497_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4497_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
lean_ctor_set_tag(v___x_4510_, 0);
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
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
lean_object* v_a_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_a_4516_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4516_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4518_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4474_, v___x_4517_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_a_4516_);
lean_dec(v_a_4495_);
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4521_ = v___x_4518_;
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4518_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4523_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4524_ = lean_string_append(v___x_4523_, v_a_4519_);
lean_dec(v_a_4519_);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 0, v___x_4524_);
v___x_4526_ = v___x_4521_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4524_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_a_4516_);
lean_dec(v_a_4495_);
v_a_4529_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4518_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4518_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 0);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4546_; 
v_a_4537_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4539_ = v___x_4518_;
v_isShared_4540_ = v_isSharedCheck_4546_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4518_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4546_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; uint8_t v___x_4542_; lean_object* v___x_4544_; 
v___x_4541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4541_, 0, v_a_4495_);
lean_ctor_set(v___x_4541_, 1, v_a_4516_);
v___x_4542_ = lean_unbox(v_a_4537_);
lean_dec(v_a_4537_);
lean_ctor_set_uint8(v___x_4541_, sizeof(void*)*2, v___x_4542_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4544_ = v___x_4539_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4541_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4549_){
_start:
{
lean_object* v_module_4550_; lean_object* v_decl_4551_; uint8_t v_isExactMatch_4552_; lean_object* v___x_4553_; uint8_t v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_module_4550_ = lean_ctor_get(v_x_4549_, 0);
lean_inc(v_module_4550_);
v_decl_4551_ = lean_ctor_get(v_x_4549_, 1);
lean_inc(v_decl_4551_);
v_isExactMatch_4552_ = lean_ctor_get_uint8(v_x_4549_, sizeof(void*)*2);
lean_dec_ref(v_x_4549_);
v___x_4553_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4554_ = 1;
v___x_4555_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4550_, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4553_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
v___x_4558_ = lean_box(0);
v___x_4559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4557_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
v___x_4560_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4551_, v___x_4554_);
v___x_4562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4560_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
lean_ctor_set(v___x_4564_, 1, v___x_4558_);
v___x_4565_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4566_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4566_, 0, v_isExactMatch_4552_);
v___x_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
lean_ctor_set(v___x_4568_, 1, v___x_4558_);
v___x_4569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
lean_ctor_set(v___x_4569_, 1, v___x_4558_);
v___x_4570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4564_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4559_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4573_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4571_, v___x_4572_);
v___x_4574_ = l_Lean_Json_mkObj(v___x_4573_);
lean_dec(v___x_4573_);
return v___x_4574_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4577_, size_t v_i_4578_, lean_object* v_bs_4579_){
_start:
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_usize_dec_lt(v_i_4578_, v_sz_4577_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
v___x_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_bs_4579_);
return v___x_4581_;
}
else
{
lean_object* v_v_4582_; lean_object* v___x_4583_; 
v_v_4582_ = lean_array_uget_borrowed(v_bs_4579_, v_i_4578_);
lean_inc(v_v_4582_);
v___x_4583_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4582_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_bs_4579_);
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4593_; lean_object* v_bs_x27_4594_; size_t v___x_4595_; size_t v___x_4596_; lean_object* v___x_4597_; 
v_a_4592_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4583_, 1);
v___x_4593_ = lean_unsigned_to_nat(0u);
v_bs_x27_4594_ = lean_array_uset(v_bs_4579_, v_i_4578_, v___x_4593_);
v___x_4595_ = ((size_t)1ULL);
v___x_4596_ = lean_usize_add(v_i_4578_, v___x_4595_);
v___x_4597_ = lean_array_uset(v_bs_x27_4594_, v_i_4578_, v_a_4592_);
v_i_4578_ = v___x_4596_;
v_bs_4579_ = v___x_4597_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4577_ = stack[0].m_num;
size_t v_i_4578_ = stack[1].m_num;
lean_object* v_bs_4579_ = stack[2].m_obj;
lean_object* v_res_4599_;
v_res_4599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4577_, v_i_4578_, v_bs_4579_);
stack->m_obj
 = v_res_4599_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4600_, lean_object* v_i_4601_, lean_object* v_bs_4602_){
_start:
{
size_t v_sz_boxed_4603_; size_t v_i_boxed_4604_; lean_object* v_res_4605_; 
v_sz_boxed_4603_ = lean_unbox_usize(v_sz_4600_);
lean_dec(v_sz_4600_);
v_i_boxed_4604_ = lean_unbox_usize(v_i_4601_);
lean_dec(v_i_4601_);
v_res_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4603_, v_i_boxed_4604_, v_bs_4602_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4606_){
_start:
{
if (lean_obj_tag(v_x_4606_) == 4)
{
lean_object* v_elems_4607_; size_t v_sz_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v_elems_4607_ = lean_ctor_get(v_x_4606_, 0);
lean_inc_ref(v_elems_4607_);
lean_dec_ref_known(v_x_4606_, 1);
v_sz_4608_ = lean_array_size(v_elems_4607_);
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4608_, v___x_4609_, v_elems_4607_);
return v___x_4610_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4611_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4612_ = lean_unsigned_to_nat(80u);
v___x_4613_ = l_Lean_Json_pretty(v_x_4606_, v___x_4612_);
v___x_4614_ = lean_string_append(v___x_4611_, v___x_4613_);
lean_dec_ref(v___x_4613_);
v___x_4615_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4616_ = lean_string_append(v___x_4614_, v___x_4615_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4618_, size_t v_i_4619_, lean_object* v_bs_4620_){
_start:
{
uint8_t v___x_4621_; 
v___x_4621_ = lean_usize_dec_lt(v_i_4619_, v_sz_4618_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_bs_4620_);
return v___x_4622_;
}
else
{
lean_object* v_v_4623_; lean_object* v___x_4624_; 
v_v_4623_ = lean_array_uget_borrowed(v_bs_4620_, v_i_4619_);
lean_inc(v_v_4623_);
v___x_4624_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4623_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec_ref(v_bs_4620_);
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4634_; lean_object* v_bs_x27_4635_; size_t v___x_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v_a_4633_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4634_ = lean_unsigned_to_nat(0u);
v_bs_x27_4635_ = lean_array_uset(v_bs_4620_, v_i_4619_, v___x_4634_);
v___x_4636_ = ((size_t)1ULL);
v___x_4637_ = lean_usize_add(v_i_4619_, v___x_4636_);
v___x_4638_ = lean_array_uset(v_bs_x27_4635_, v_i_4619_, v_a_4633_);
v_i_4619_ = v___x_4637_;
v_bs_4620_ = v___x_4638_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4618_ = stack[0].m_num;
size_t v_i_4619_ = stack[1].m_num;
lean_object* v_bs_4620_ = stack[2].m_obj;
lean_object* v_res_4640_;
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4618_, v_i_4619_, v_bs_4620_);
stack->m_obj
 = v_res_4640_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4641_, lean_object* v_i_4642_, lean_object* v_bs_4643_){
_start:
{
size_t v_sz_boxed_4644_; size_t v_i_boxed_4645_; lean_object* v_res_4646_; 
v_sz_boxed_4644_ = lean_unbox_usize(v_sz_4641_);
lean_dec(v_sz_4641_);
v_i_boxed_4645_ = lean_unbox_usize(v_i_4642_);
lean_dec(v_i_4642_);
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4644_, v_i_boxed_4645_, v_bs_4643_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4647_){
_start:
{
if (lean_obj_tag(v_x_4647_) == 4)
{
lean_object* v_elems_4648_; size_t v_sz_4649_; size_t v___x_4650_; lean_object* v___x_4651_; 
v_elems_4648_ = lean_ctor_get(v_x_4647_, 0);
lean_inc_ref(v_elems_4648_);
lean_dec_ref_known(v_x_4647_, 1);
v_sz_4649_ = lean_array_size(v_elems_4648_);
v___x_4650_ = ((size_t)0ULL);
v___x_4651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4649_, v___x_4650_, v_elems_4648_);
return v___x_4651_;
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4652_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4653_ = lean_unsigned_to_nat(80u);
v___x_4654_ = l_Lean_Json_pretty(v_x_4647_, v___x_4653_);
v___x_4655_ = lean_string_append(v___x_4652_, v___x_4654_);
lean_dec_ref(v___x_4654_);
v___x_4656_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4657_ = lean_string_append(v___x_4655_, v___x_4656_);
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
return v___x_4658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4659_, lean_object* v_k_4660_){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = l_Lean_Json_getObjValD(v_j_4659_, v_k_4660_);
v___x_4662_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4663_, lean_object* v_k_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4663_, v_k_4664_);
lean_dec_ref(v_k_4664_);
return v_res_4665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = 1;
v___x_4673_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4673_, v___x_4672_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4677_ = lean_string_append(v___x_4676_, v___x_4675_);
return v___x_4677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4680_ = 1;
v___x_4681_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4681_, v___x_4680_);
return v___x_4682_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4684_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4685_ = lean_string_append(v___x_4684_, v___x_4683_);
return v___x_4685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4688_ = lean_string_append(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4689_){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4691_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4689_, v___x_4690_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4701_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4694_ = v___x_4691_;
v_isShared_4695_ = v_isSharedCheck_4701_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4701_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4697_ = lean_string_append(v___x_4696_, v_a_4692_);
lean_dec(v_a_4692_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4697_);
v___x_4699_ = v___x_4694_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
else
{
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
v_a_4702_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4691_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4691_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 0);
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
v_a_4710_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4691_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4691_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4720_, size_t v_i_4721_, lean_object* v_bs_4722_){
_start:
{
uint8_t v___x_4723_; 
v___x_4723_ = lean_usize_dec_lt(v_i_4721_, v_sz_4720_);
if (v___x_4723_ == 0)
{
return v_bs_4722_;
}
else
{
lean_object* v_v_4724_; lean_object* v___x_4725_; lean_object* v_bs_x27_4726_; lean_object* v___x_4727_; size_t v___x_4728_; size_t v___x_4729_; lean_object* v___x_4730_; 
v_v_4724_ = lean_array_uget(v_bs_4722_, v_i_4721_);
v___x_4725_ = lean_unsigned_to_nat(0u);
v_bs_x27_4726_ = lean_array_uset(v_bs_4722_, v_i_4721_, v___x_4725_);
v___x_4727_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4724_);
v___x_4728_ = ((size_t)1ULL);
v___x_4729_ = lean_usize_add(v_i_4721_, v___x_4728_);
v___x_4730_ = lean_array_uset(v_bs_x27_4726_, v_i_4721_, v___x_4727_);
v_i_4721_ = v___x_4729_;
v_bs_4722_ = v___x_4730_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4720_ = stack[0].m_num;
size_t v_i_4721_ = stack[1].m_num;
lean_object* v_bs_4722_ = stack[2].m_obj;
lean_object* v_res_4732_;
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4720_, v_i_4721_, v_bs_4722_);
stack->m_obj
 = v_res_4732_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4733_, lean_object* v_i_4734_, lean_object* v_bs_4735_){
_start:
{
size_t v_sz_boxed_4736_; size_t v_i_boxed_4737_; lean_object* v_res_4738_; 
v_sz_boxed_4736_ = lean_unbox_usize(v_sz_4733_);
lean_dec(v_sz_4733_);
v_i_boxed_4737_ = lean_unbox_usize(v_i_4734_);
lean_dec(v_i_4734_);
v_res_4738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4736_, v_i_boxed_4737_, v_bs_4735_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4739_){
_start:
{
size_t v_sz_4740_; size_t v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_sz_4740_ = lean_array_size(v_a_4739_);
v___x_4741_ = ((size_t)0ULL);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4740_, v___x_4741_, v_a_4739_);
v___x_4743_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4742_);
return v___x_4743_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4744_, size_t v_i_4745_, lean_object* v_bs_4746_){
_start:
{
uint8_t v___x_4747_; 
v___x_4747_ = lean_usize_dec_lt(v_i_4745_, v_sz_4744_);
if (v___x_4747_ == 0)
{
return v_bs_4746_;
}
else
{
lean_object* v_v_4748_; lean_object* v___x_4749_; lean_object* v_bs_x27_4750_; lean_object* v___x_4751_; size_t v___x_4752_; size_t v___x_4753_; lean_object* v___x_4754_; 
v_v_4748_ = lean_array_uget(v_bs_4746_, v_i_4745_);
v___x_4749_ = lean_unsigned_to_nat(0u);
v_bs_x27_4750_ = lean_array_uset(v_bs_4746_, v_i_4745_, v___x_4749_);
v___x_4751_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4748_);
v___x_4752_ = ((size_t)1ULL);
v___x_4753_ = lean_usize_add(v_i_4745_, v___x_4752_);
v___x_4754_ = lean_array_uset(v_bs_x27_4750_, v_i_4745_, v___x_4751_);
v_i_4745_ = v___x_4753_;
v_bs_4746_ = v___x_4754_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4744_ = stack[0].m_num;
size_t v_i_4745_ = stack[1].m_num;
lean_object* v_bs_4746_ = stack[2].m_obj;
lean_object* v_res_4756_;
v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4744_, v_i_4745_, v_bs_4746_);
stack->m_obj
 = v_res_4756_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4757_, lean_object* v_i_4758_, lean_object* v_bs_4759_){
_start:
{
size_t v_sz_boxed_4760_; size_t v_i_boxed_4761_; lean_object* v_res_4762_; 
v_sz_boxed_4760_ = lean_unbox_usize(v_sz_4757_);
lean_dec(v_sz_4757_);
v_i_boxed_4761_ = lean_unbox_usize(v_i_4758_);
lean_dec(v_i_4758_);
v_res_4762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4760_, v_i_boxed_4761_, v_bs_4759_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4763_){
_start:
{
size_t v_sz_4764_; size_t v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v_sz_4764_ = lean_array_size(v_a_4763_);
v___x_4765_ = ((size_t)0ULL);
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4764_, v___x_4765_, v_a_4763_);
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
v___x_4770_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4768_);
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
lean_dec(v___x_4776_);
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
lean_dec_ref_known(v___x_4809_, 1);
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
lean_dec(v___x_4882_);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4897_){
_start:
{
if (lean_obj_tag(v_x_4897_) == 0)
{
lean_object* v___x_4898_; 
v___x_4898_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
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
v___x_4920_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4919_);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4926_){
_start:
{
if (lean_obj_tag(v_x_4926_) == 0)
{
lean_object* v___x_4927_; 
v___x_4927_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
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
v___x_4949_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4948_);
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
lean_dec_ref_known(v___x_5040_, 1);
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
lean_dec_ref_known(v___x_5061_, 1);
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
lean_dec_ref_known(v___x_5082_, 1);
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
lean_dec_ref_known(v___x_5103_, 1);
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
lean_dec_ref_known(v___x_5124_, 1);
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
lean_dec_ref_known(v_x_5178_, 1);
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
lean_dec_ref_known(v_x_5186_, 1);
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
lean_dec(v___x_5229_);
return v___x_5230_;
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

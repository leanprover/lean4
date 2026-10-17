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
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl(lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_obj_tag_nat(v_x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorIdx___impl(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(lean_object* v_t_215_, lean_object* v_k_216_){
_start:
{
lean_object* v_m_217_; lean_object* v_n_218_; lean_object* v___x_219_; 
v_m_217_ = lean_ctor_get(v_t_215_, 0);
lean_inc_ref(v_m_217_);
v_n_218_ = lean_ctor_get(v_t_215_, 1);
lean_inc_ref(v_n_218_);
lean_dec_ref(v_t_215_);
v___x_219_ = lean_apply_2(v_k_216_, v_m_217_, v_n_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_222_, v_k_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___boxed(lean_object* v_motive_226_, lean_object* v_ctorIdx_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim(v_motive_226_, v_ctorIdx_227_, v_t_228_, v_h_229_, v_k_230_);
lean_dec(v_ctorIdx_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim___redArg(lean_object* v_t_232_, lean_object* v_c_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_232_, v_c_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_c_elim(lean_object* v_motive_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_c_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_236_, v_c_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim___redArg(lean_object* v_t_240_, lean_object* v_f_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_240_, v_f_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_RefIdentJsonRepr_f_elim(lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_f_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Lsp_RefIdent_RefIdentJsonRepr_ctorElim___redArg(v_t_244_, v_f_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(lean_object* v_json_281_){
_start:
{
lean_object* v___x_282_; 
lean_inc(v_json_281_);
v___x_282_ = l_Lean_Json_getTag_x3f(v_json_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_283_; 
lean_dec(v_json_281_);
v___x_283_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__1));
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_val_284_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_282_, 1);
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_287_ = lean_string_dec_eq(v_val_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_289_ = lean_string_dec_eq(v_val_284_, v___x_288_);
lean_dec(v_val_284_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec(v_json_281_);
v___x_290_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__5));
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_unsigned_to_nat(2u);
v___x_292_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__11));
v___x_293_ = l_Lean_Json_parseCtorFields(v_json_281_, v___x_288_, v___x_291_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_a_302_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_293_, 1);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_array_get_borrowed(v___x_285_, v_a_302_, v___x_303_);
lean_inc(v___x_304_);
v___x_305_ = l_Lean_Json_getStr_x3f(v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_a_302_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_a_314_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_305_, 1);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_array_get(v___x_285_, v_a_302_, v___x_315_);
lean_dec(v_a_302_);
v___x_317_ = l_Lean_Json_getStr_x3f(v___x_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_a_314_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_a_326_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v___x_317_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_317_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_a_314_);
lean_ctor_set(v___x_330_, 1, v_a_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_val_284_);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__15));
v___x_337_ = l_Lean_Json_parseCtorFields(v_json_281_, v___x_286_, v___x_335_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_346_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_337_, 1);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_array_get_borrowed(v___x_285_, v_a_346_, v___x_347_);
lean_inc(v___x_348_);
v___x_349_ = l_Lean_Json_getStr_x3f(v___x_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_346_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_358_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_349_, 1);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_array_get(v___x_285_, v_a_346_, v___x_359_);
lean_dec(v_a_346_);
v___x_361_ = l_Lean_Json_getStr_x3f(v___x_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_358_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_a_370_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_378_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v_a_358_);
lean_ctor_set(v___x_374_, 1, v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_m_382_; lean_object* v_n_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_403_; 
v_m_382_ = lean_ctor_get(v_x_381_, 0);
v_n_383_ = lean_ctor_get(v_x_381_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_403_ == 0)
{
v___x_385_ = v_x_381_;
v_isShared_386_ = v_isSharedCheck_403_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_n_383_);
lean_inc(v_m_382_);
lean_dec(v_x_381_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_403_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_387_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__3));
v___x_388_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_389_, 0, v_m_382_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v___x_389_);
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_391_ = v___x_385_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_402_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_392_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__8));
v___x_393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_393_, 0, v_n_383_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_391_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_Json_mkObj(v___x_397_);
lean_dec_ref_known(v___x_397_, 2);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_387_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_395_);
v___x_401_ = l_Lean_Json_mkObj(v___x_400_);
lean_dec_ref_known(v___x_400_, 2);
return v___x_401_;
}
}
}
else
{
lean_object* v_m_404_; lean_object* v_i_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_425_; 
v_m_404_ = lean_ctor_get(v_x_381_, 0);
v_i_405_ = lean_ctor_get(v_x_381_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_425_ == 0)
{
v___x_407_ = v_x_381_;
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_i_405_);
lean_inc(v_m_404_);
lean_dec(v_x_381_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_425_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_409_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__2));
v___x_410_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__6));
v___x_411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_411_, 0, v_m_404_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 1, v___x_411_);
lean_ctor_set(v___x_407_, 0, v___x_410_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_424_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_414_ = ((lean_object*)(l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson___closed__12));
v___x_415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_415_, 0, v_i_405_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_413_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Lean_Json_mkObj(v___x_419_);
lean_dec_ref_known(v___x_419_, 2);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_409_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_417_);
v___x_423_ = l_Lean_Json_mkObj(v___x_422_);
lean_dec_ref_known(v___x_422_, 2);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJsonRepr(lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v_moduleName_429_; lean_object* v_identName_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_moduleName_429_ = lean_ctor_get(v_x_428_, 0);
v_identName_430_ = lean_ctor_get(v_x_428_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v_x_428_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_identName_430_);
lean_inc(v_moduleName_429_);
lean_dec(v_x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_moduleName_429_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_identName_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_moduleName_438_; lean_object* v_id_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_moduleName_438_ = lean_ctor_get(v_x_428_, 0);
v_id_439_ = lean_ctor_get(v_x_428_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v_x_428_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_id_439_);
lean_inc(v_moduleName_438_);
lean_dec(v_x_428_);
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
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_moduleName_438_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_id_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJsonRepr(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_m_448_; lean_object* v_n_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_m_448_ = lean_ctor_get(v_x_447_, 0);
v_n_449_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v_x_447_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_n_449_);
lean_inc(v_m_448_);
lean_dec(v_x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_m_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_n_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_m_457_; lean_object* v_i_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_m_457_ = lean_ctor_get(v_x_447_, 0);
v_i_458_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v_x_447_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_i_458_);
lean_inc(v_m_457_);
lean_dec(v_x_447_);
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
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_m_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_i_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_fromJson_x3f(lean_object* v_s_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Lsp_RefIdent_instFromJsonRefIdentJsonRepr_fromJson(v_s_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_484_; 
v_a_476_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_484_ == 0)
{
v___x_478_ = v___x_467_;
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_467_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_484_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = l_Lean_Lsp_RefIdent_fromJsonRepr(v_a_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefIdent_toJson(lean_object* v_id_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = l_Lean_Lsp_RefIdent_toJsonRepr(v_id_485_);
v___x_487_ = l_Lean_Lsp_RefIdent_instToJsonRefIdentJsonRepr_toJson(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges(lean_object* v_r_492_){
_start:
{
lean_object* v_range_493_; lean_object* v_pos_494_; lean_object* v_endPos_495_; lean_object* v_selectionRange_496_; lean_object* v_pos_497_; lean_object* v_endPos_498_; lean_object* v_charUtf16_499_; lean_object* v_endCharUtf16_500_; lean_object* v_line_501_; lean_object* v_line_502_; lean_object* v_charUtf16_503_; lean_object* v_endCharUtf16_504_; lean_object* v_line_505_; lean_object* v_line_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_range_493_ = lean_ctor_get(v_r_492_, 0);
v_pos_494_ = lean_ctor_get(v_range_493_, 0);
v_endPos_495_ = lean_ctor_get(v_range_493_, 2);
v_selectionRange_496_ = lean_ctor_get(v_r_492_, 1);
v_pos_497_ = lean_ctor_get(v_selectionRange_496_, 0);
v_endPos_498_ = lean_ctor_get(v_selectionRange_496_, 2);
v_charUtf16_499_ = lean_ctor_get(v_range_493_, 1);
v_endCharUtf16_500_ = lean_ctor_get(v_range_493_, 3);
v_line_501_ = lean_ctor_get(v_pos_494_, 0);
v_line_502_ = lean_ctor_get(v_endPos_495_, 0);
v_charUtf16_503_ = lean_ctor_get(v_selectionRange_496_, 1);
v_endCharUtf16_504_ = lean_ctor_get(v_selectionRange_496_, 3);
v_line_505_ = lean_ctor_get(v_pos_497_, 0);
v_line_506_ = lean_ctor_get(v_endPos_498_, 0);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v_line_501_, v___x_507_);
v___x_509_ = lean_nat_sub(v_line_502_, v___x_507_);
v___x_510_ = lean_nat_sub(v_line_505_, v___x_507_);
v___x_511_ = lean_nat_sub(v_line_506_, v___x_507_);
lean_inc(v_endCharUtf16_504_);
lean_inc(v_charUtf16_503_);
lean_inc(v_endCharUtf16_500_);
lean_inc(v_charUtf16_499_);
v___x_512_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_512_, 0, v___x_508_);
lean_ctor_set(v___x_512_, 1, v_charUtf16_499_);
lean_ctor_set(v___x_512_, 2, v___x_509_);
lean_ctor_set(v___x_512_, 3, v_endCharUtf16_500_);
lean_ctor_set(v___x_512_, 4, v___x_510_);
lean_ctor_set(v___x_512_, 5, v_charUtf16_503_);
lean_ctor_set(v___x_512_, 6, v___x_511_);
lean_ctor_set(v___x_512_, 7, v_endCharUtf16_504_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_ofDeclarationRanges___boxed(lean_object* v_r_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Lsp_DeclInfo_ofDeclarationRanges(v_r_513_);
lean_dec_ref(v_r_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range(lean_object* v_i_515_){
_start:
{
lean_object* v_rangeStartPosLine_516_; lean_object* v_rangeStartPosCharacter_517_; lean_object* v_rangeEndPosLine_518_; lean_object* v_rangeEndPosCharacter_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_rangeStartPosLine_516_ = lean_ctor_get(v_i_515_, 0);
v_rangeStartPosCharacter_517_ = lean_ctor_get(v_i_515_, 1);
v_rangeEndPosLine_518_ = lean_ctor_get(v_i_515_, 2);
v_rangeEndPosCharacter_519_ = lean_ctor_get(v_i_515_, 3);
lean_inc(v_rangeStartPosCharacter_517_);
lean_inc(v_rangeStartPosLine_516_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_rangeStartPosLine_516_);
lean_ctor_set(v___x_520_, 1, v_rangeStartPosCharacter_517_);
lean_inc(v_rangeEndPosCharacter_519_);
lean_inc(v_rangeEndPosLine_518_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_rangeEndPosLine_518_);
lean_ctor_set(v___x_521_, 1, v_rangeEndPosCharacter_519_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_range___boxed(lean_object* v_i_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Lsp_DeclInfo_range(v_i_523_);
lean_dec_ref(v_i_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange(lean_object* v_i_525_){
_start:
{
lean_object* v_selectionRangeStartPosLine_526_; lean_object* v_selectionRangeStartPosCharacter_527_; lean_object* v_selectionRangeEndPosLine_528_; lean_object* v_selectionRangeEndPosCharacter_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_selectionRangeStartPosLine_526_ = lean_ctor_get(v_i_525_, 4);
v_selectionRangeStartPosCharacter_527_ = lean_ctor_get(v_i_525_, 5);
v_selectionRangeEndPosLine_528_ = lean_ctor_get(v_i_525_, 6);
v_selectionRangeEndPosCharacter_529_ = lean_ctor_get(v_i_525_, 7);
lean_inc(v_selectionRangeStartPosCharacter_527_);
lean_inc(v_selectionRangeStartPosLine_526_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_selectionRangeStartPosLine_526_);
lean_ctor_set(v___x_530_, 1, v_selectionRangeStartPosCharacter_527_);
lean_inc(v_selectionRangeEndPosCharacter_529_);
lean_inc(v_selectionRangeEndPosLine_528_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_selectionRangeEndPosLine_528_);
lean_ctor_set(v___x_531_, 1, v_selectionRangeEndPosCharacter_529_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeclInfo_selectionRange___boxed(lean_object* v_i_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Lsp_DeclInfo_selectionRange(v_i_533_);
lean_dec_ref(v_i_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeclInfo___lam__0(lean_object* v_i_535_){
_start:
{
lean_object* v_rangeStartPosLine_536_; lean_object* v_rangeStartPosCharacter_537_; lean_object* v_rangeEndPosLine_538_; lean_object* v_rangeEndPosCharacter_539_; lean_object* v_selectionRangeStartPosLine_540_; lean_object* v_selectionRangeStartPosCharacter_541_; lean_object* v_selectionRangeEndPosLine_542_; lean_object* v_selectionRangeEndPosCharacter_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_rangeStartPosLine_536_ = lean_ctor_get(v_i_535_, 0);
lean_inc(v_rangeStartPosLine_536_);
v_rangeStartPosCharacter_537_ = lean_ctor_get(v_i_535_, 1);
lean_inc(v_rangeStartPosCharacter_537_);
v_rangeEndPosLine_538_ = lean_ctor_get(v_i_535_, 2);
lean_inc(v_rangeEndPosLine_538_);
v_rangeEndPosCharacter_539_ = lean_ctor_get(v_i_535_, 3);
lean_inc(v_rangeEndPosCharacter_539_);
v_selectionRangeStartPosLine_540_ = lean_ctor_get(v_i_535_, 4);
lean_inc(v_selectionRangeStartPosLine_540_);
v_selectionRangeStartPosCharacter_541_ = lean_ctor_get(v_i_535_, 5);
lean_inc(v_selectionRangeStartPosCharacter_541_);
v_selectionRangeEndPosLine_542_ = lean_ctor_get(v_i_535_, 6);
lean_inc(v_selectionRangeEndPosLine_542_);
v_selectionRangeEndPosCharacter_543_ = lean_ctor_get(v_i_535_, 7);
lean_inc(v_selectionRangeEndPosCharacter_543_);
lean_dec_ref(v_i_535_);
v___x_544_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_536_);
v___x_545_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___x_546_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_537_);
v___x_547_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_538_);
v___x_549_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
v___x_550_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_539_);
v___x_551_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_540_);
v___x_553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_541_);
v___x_555_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_542_);
v___x_557_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_543_);
v___x_559_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(8u);
v___x_561_ = lean_mk_empty_array_with_capacity(v___x_560_);
v___x_562_ = lean_array_push(v___x_561_, v___x_545_);
v___x_563_ = lean_array_push(v___x_562_, v___x_547_);
v___x_564_ = lean_array_push(v___x_563_, v___x_549_);
v___x_565_ = lean_array_push(v___x_564_, v___x_551_);
v___x_566_ = lean_array_push(v___x_565_, v___x_553_);
v___x_567_ = lean_array_push(v___x_566_, v___x_555_);
v___x_568_ = lean_array_push(v___x_567_, v___x_557_);
v___x_569_ = lean_array_push(v___x_568_, v___x_559_);
v___x_570_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0(lean_object* v___x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 4)
{
lean_object* v_elems_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_696_; 
v_elems_579_ = lean_ctor_get(v_x_578_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_696_ == 0)
{
v___x_581_ = v_x_578_;
v_isShared_582_ = v_isSharedCheck_696_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_elems_579_);
lean_dec(v_x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_696_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_array_get_size(v_elems_579_);
v___x_584_ = lean_unsigned_to_nat(8u);
v___x_585_ = lean_nat_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec_ref(v_elems_579_);
v___x_586_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_587_ = l_Nat_reprFast(v___x_583_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
lean_ctor_set(v___x_581_, 0, v___x_588_);
v___x_590_ = v___x_581_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_581_);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_592_);
lean_inc(v___x_593_);
v___x_594_ = l_Lean_Json_getNat_x3f(v___x_593_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_elems_579_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_594_, 1);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_604_);
lean_inc(v___x_605_);
v___x_606_ = l_Lean_Json_getNat_x3f(v___x_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_615_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_606_, 1);
v___x_616_ = lean_unsigned_to_nat(2u);
v___x_617_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_616_);
lean_inc(v___x_617_);
v___x_618_ = l_Lean_Json_getNat_x3f(v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_a_615_);
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_627_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_618_, 1);
v___x_628_ = lean_unsigned_to_nat(3u);
v___x_629_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_628_);
lean_inc(v___x_629_);
v___x_630_ = l_Lean_Json_getNat_x3f(v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_627_);
lean_dec(v_a_615_);
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_639_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_630_, 1);
v___x_640_ = lean_unsigned_to_nat(4u);
v___x_641_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_640_);
lean_inc(v___x_641_);
v___x_642_ = l_Lean_Json_getNat_x3f(v___x_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_a_639_);
lean_dec(v_a_627_);
lean_dec(v_a_615_);
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_a_651_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_642_, 1);
v___x_652_ = lean_unsigned_to_nat(5u);
v___x_653_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_652_);
lean_inc(v___x_653_);
v___x_654_ = l_Lean_Json_getNat_x3f(v___x_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v_a_651_);
lean_dec(v_a_639_);
lean_dec(v_a_627_);
lean_dec(v_a_615_);
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_663_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_654_, 1);
v___x_664_ = lean_unsigned_to_nat(6u);
v___x_665_ = lean_array_get_borrowed(v___x_577_, v_elems_579_, v___x_664_);
lean_inc(v___x_665_);
v___x_666_ = l_Lean_Json_getNat_x3f(v___x_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_663_);
lean_dec(v_a_651_);
lean_dec(v_a_639_);
lean_dec(v_a_627_);
lean_dec(v_a_615_);
lean_dec(v_a_603_);
lean_dec_ref(v_elems_579_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_a_675_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_666_, 1);
v___x_676_ = lean_unsigned_to_nat(7u);
v___x_677_ = lean_array_get(v___x_577_, v_elems_579_, v___x_676_);
lean_dec_ref(v_elems_579_);
v___x_678_ = l_Lean_Json_getNat_x3f(v___x_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_a_675_);
lean_dec(v_a_663_);
lean_dec(v_a_651_);
lean_dec(v_a_639_);
lean_dec(v_a_627_);
lean_dec(v_a_615_);
lean_dec(v_a_603_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_a_687_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_678_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_678_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_691_, 0, v_a_603_);
lean_ctor_set(v___x_691_, 1, v_a_615_);
lean_ctor_set(v___x_691_, 2, v_a_627_);
lean_ctor_set(v___x_691_, 3, v_a_639_);
lean_ctor_set(v___x_691_, 4, v_a_651_);
lean_ctor_set(v___x_691_, 5, v_a_663_);
lean_ctor_set(v___x_691_, 6, v_a_675_);
lean_ctor_set(v___x_691_, 7, v_a_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
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
lean_object* v___x_697_; 
lean_dec(v_x_578_);
v___x_697_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeclInfo___lam__0___boxed(lean_object* v___x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Lsp_instFromJsonDeclInfo___lam__0(v___x_698_, v_x_699_);
lean_dec(v___x_698_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(1);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(1);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_706_, lean_object* v_a_707_, lean_object* v_b_708_, lean_object* v_c_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_a_707_);
lean_ctor_set(v___x_710_, 1, v_b_708_);
v___x_711_ = lean_apply_2(v_f_706_, v___x_710_, v_c_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_731_, lean_object* v_init_732_, lean_object* v_f_733_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_a_737_; 
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_734_, 0, v_f_733_);
v___x_735_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_736_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_735_, v___f_734_, v_init_732_, v_m_731_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec(v___x_736_);
return v_a_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_738_, lean_object* v_m_739_, lean_object* v_init_740_, lean_object* v_f_741_){
_start:
{
lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_a_745_; 
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_742_, 0, v_f_741_);
v___x_743_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_744_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_743_, v___f_742_, v_init_740_, v_m_739_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec(v___x_744_);
return v_a_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_746_, lean_object* v_init_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_k_749_; lean_object* v_v_750_; lean_object* v_l_751_; lean_object* v_r_752_; lean_object* v___x_753_; 
v_k_749_ = lean_ctor_get(v_x_748_, 1);
v_v_750_ = lean_ctor_get(v_x_748_, 2);
v_l_751_ = lean_ctor_get(v_x_748_, 3);
v_r_752_ = lean_ctor_get(v_x_748_, 4);
lean_inc_ref(v___y_746_);
v___x_753_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_746_, v_init_747_, v_l_751_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_dec_ref(v___y_746_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
lean_inc(v_v_750_);
lean_inc(v_k_749_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_k_749_);
lean_ctor_set(v___x_755_, 1, v_v_750_);
lean_inc_ref(v___y_746_);
v___x_756_ = lean_apply_2(v___y_746_, v___x_755_, v_a_754_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_dec_ref(v___y_746_);
return v___x_756_;
}
else
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v_init_747_ = v_a_757_;
v_x_748_ = v_r_752_;
goto _start;
}
}
}
else
{
lean_object* v___x_759_; 
lean_dec_ref(v___y_746_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v_init_747_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_760_, lean_object* v_init_761_, lean_object* v_x_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_760_, v_init_761_, v_x_762_);
lean_dec(v_x_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_768_; lean_object* v_a_769_; 
v___x_768_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_767_, v___y_766_, v___y_765_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
return v_a_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v_init_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_778_, v_init_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v_init_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_782_, v___y_783_, v_init_784_, v_x_785_);
lean_dec(v_x_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_787_){
_start:
{
lean_object* v_snd_788_; lean_object* v_fst_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_831_; 
v_snd_788_ = lean_ctor_get(v_x_787_, 1);
v_fst_789_ = lean_ctor_get(v_x_787_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_787_);
if (v_isSharedCheck_831_ == 0)
{
v___x_791_ = v_x_787_;
v_isShared_792_ = v_isSharedCheck_831_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_789_);
lean_dec(v_x_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_831_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_rangeStartPosLine_793_; lean_object* v_rangeStartPosCharacter_794_; lean_object* v_rangeEndPosLine_795_; lean_object* v_rangeEndPosCharacter_796_; lean_object* v_selectionRangeStartPosLine_797_; lean_object* v_selectionRangeStartPosCharacter_798_; lean_object* v_selectionRangeEndPosLine_799_; lean_object* v_selectionRangeEndPosCharacter_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v_rangeStartPosLine_793_ = lean_ctor_get(v_snd_788_, 0);
lean_inc(v_rangeStartPosLine_793_);
v_rangeStartPosCharacter_794_ = lean_ctor_get(v_snd_788_, 1);
lean_inc(v_rangeStartPosCharacter_794_);
v_rangeEndPosLine_795_ = lean_ctor_get(v_snd_788_, 2);
lean_inc(v_rangeEndPosLine_795_);
v_rangeEndPosCharacter_796_ = lean_ctor_get(v_snd_788_, 3);
lean_inc(v_rangeEndPosCharacter_796_);
v_selectionRangeStartPosLine_797_ = lean_ctor_get(v_snd_788_, 4);
lean_inc(v_selectionRangeStartPosLine_797_);
v_selectionRangeStartPosCharacter_798_ = lean_ctor_get(v_snd_788_, 5);
lean_inc(v_selectionRangeStartPosCharacter_798_);
v_selectionRangeEndPosLine_799_ = lean_ctor_get(v_snd_788_, 6);
lean_inc(v_selectionRangeEndPosLine_799_);
v_selectionRangeEndPosCharacter_800_ = lean_ctor_get(v_snd_788_, 7);
lean_inc(v_selectionRangeEndPosCharacter_800_);
lean_dec(v_snd_788_);
v___x_801_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_793_);
v___x_802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_794_);
v___x_804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_795_);
v___x_806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_796_);
v___x_808_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_797_);
v___x_810_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_798_);
v___x_812_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_799_);
v___x_814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_800_);
v___x_816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = lean_unsigned_to_nat(8u);
v___x_818_ = lean_mk_empty_array_with_capacity(v___x_817_);
v___x_819_ = lean_array_push(v___x_818_, v___x_802_);
v___x_820_ = lean_array_push(v___x_819_, v___x_804_);
v___x_821_ = lean_array_push(v___x_820_, v___x_806_);
v___x_822_ = lean_array_push(v___x_821_, v___x_808_);
v___x_823_ = lean_array_push(v___x_822_, v___x_810_);
v___x_824_ = lean_array_push(v___x_823_, v___x_812_);
v___x_825_ = lean_array_push(v___x_824_, v___x_814_);
v___x_826_ = lean_array_push(v___x_825_, v___x_816_);
v___x_827_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_827_);
v___x_829_ = v___x_791_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_832_, lean_object* v_x2_833_, lean_object* v_x3_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_x1_832_);
lean_ctor_set(v___x_835_, 1, v_x2_833_);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_x3_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_837_, lean_object* v___f_838_, lean_object* v_m_839_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = lean_box(0);
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_842_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_841_, v___f_837_, v___x_840_, v_m_839_);
v___x_843_ = l_List_mapTR_loop___redArg(v___f_838_, v___x_842_, v___x_840_);
v___x_844_ = l_Lean_Json_mkObj(v___x_843_);
lean_dec(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v___x_853_, lean_object* v_m_854_, lean_object* v_k_855_, lean_object* v_v_856_){
_start:
{
if (lean_obj_tag(v_v_856_) == 4)
{
lean_object* v_elems_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_976_; 
v_elems_857_ = lean_ctor_get(v_v_856_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v_v_856_);
if (v_isSharedCheck_976_ == 0)
{
v___x_859_ = v_v_856_;
v_isShared_860_ = v_isSharedCheck_976_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_elems_857_);
lean_dec(v_v_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_976_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_array_get_size(v_elems_857_);
v___x_862_ = lean_unsigned_to_nat(8u);
v___x_863_ = lean_nat_dec_eq(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v___x_864_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_865_ = l_Nat_reprFast(v___x_861_);
v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
lean_dec_ref(v___x_865_);
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 0);
lean_ctor_set(v___x_859_, 0, v___x_866_);
v___x_868_ = v___x_859_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_del_object(v___x_859_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_871_);
lean_inc(v___x_872_);
v___x_873_ = l_Lean_Json_getNat_x3f(v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_882_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_873_, 1);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_883_);
lean_inc(v___x_884_);
v___x_885_ = l_Lean_Json_getNat_x3f(v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_894_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_885_, 1);
v___x_895_ = lean_unsigned_to_nat(2u);
v___x_896_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_895_);
lean_inc(v___x_896_);
v___x_897_ = l_Lean_Json_getNat_x3f(v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_a_906_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_897_, 1);
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_907_);
lean_inc(v___x_908_);
v___x_909_ = l_Lean_Json_getNat_x3f(v___x_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_906_);
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_a_918_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_909_, 1);
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_919_);
lean_inc(v___x_920_);
v___x_921_ = l_Lean_Json_getNat_x3f(v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_918_);
lean_dec(v_a_906_);
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_a_930_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_921_, 1);
v___x_931_ = lean_unsigned_to_nat(5u);
v___x_932_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_931_);
lean_inc(v___x_932_);
v___x_933_ = l_Lean_Json_getNat_x3f(v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_930_);
lean_dec(v_a_918_);
lean_dec(v_a_906_);
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_933_, 1);
v___x_943_ = lean_unsigned_to_nat(6u);
v___x_944_ = lean_array_get_borrowed(v___x_870_, v_elems_857_, v___x_943_);
lean_inc(v___x_944_);
v___x_945_ = l_Lean_Json_getNat_x3f(v___x_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_a_942_);
lean_dec(v_a_930_);
lean_dec(v_a_918_);
lean_dec(v_a_906_);
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_elems_857_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_945_, 1);
v___x_955_ = lean_unsigned_to_nat(7u);
v___x_956_ = lean_array_get(v___x_870_, v_elems_857_, v___x_955_);
lean_dec_ref(v_elems_857_);
v___x_957_ = l_Lean_Json_getNat_x3f(v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_a_954_);
lean_dec(v_a_942_);
lean_dec(v_a_930_);
lean_dec(v_a_918_);
lean_dec(v_a_906_);
lean_dec(v_a_894_);
lean_dec(v_a_882_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v_a_966_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_975_ == 0)
{
v___x_968_ = v___x_957_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_957_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_970_, 0, v_a_882_);
lean_ctor_set(v___x_970_, 1, v_a_894_);
lean_ctor_set(v___x_970_, 2, v_a_906_);
lean_ctor_set(v___x_970_, 3, v_a_918_);
lean_ctor_set(v___x_970_, 4, v_a_930_);
lean_ctor_set(v___x_970_, 5, v_a_942_);
lean_ctor_set(v___x_970_, 6, v_a_954_);
lean_ctor_set(v___x_970_, 7, v_a_966_);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_853_, v_k_855_, v___x_970_, v_m_854_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
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
lean_object* v___x_977_; 
lean_dec(v_v_856_);
lean_dec_ref(v_k_855_);
lean_dec(v_m_854_);
lean_dec_ref(v___x_853_);
v___x_977_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___x_981_, lean_object* v_j_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Json_getObj_x3f(v_j_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v___x_981_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_a_992_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_983_, 1);
v___f_993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__1));
v___x_994_ = lean_box(1);
v___x_995_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_981_, v___f_993_, v___x_994_, v_a_992_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1023_, lean_object* v_parentDecl_x3f_1024_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1024_) == 0)
{
lean_object* v_start_1025_; lean_object* v_end_1026_; lean_object* v_line_1027_; lean_object* v_character_1028_; lean_object* v_line_1029_; lean_object* v_character_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_start_1025_ = lean_ctor_get(v_range_1023_, 0);
v_end_1026_ = lean_ctor_get(v_range_1023_, 1);
v_line_1027_ = lean_ctor_get(v_start_1025_, 0);
v_character_1028_ = lean_ctor_get(v_start_1025_, 1);
v_line_1029_ = lean_ctor_get(v_end_1026_, 0);
v_character_1030_ = lean_ctor_get(v_end_1026_, 1);
v___x_1031_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1030_);
lean_inc(v_line_1029_);
lean_inc(v_character_1028_);
lean_inc(v_line_1027_);
v___x_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1032_, 0, v_line_1027_);
lean_ctor_set(v___x_1032_, 1, v_character_1028_);
lean_ctor_set(v___x_1032_, 2, v_line_1029_);
lean_ctor_set(v___x_1032_, 3, v_character_1030_);
lean_ctor_set(v___x_1032_, 4, v___x_1031_);
return v___x_1032_;
}
else
{
lean_object* v_start_1033_; lean_object* v_end_1034_; lean_object* v_line_1035_; lean_object* v_character_1036_; lean_object* v_line_1037_; lean_object* v_character_1038_; lean_object* v_val_1039_; lean_object* v___x_1040_; 
v_start_1033_ = lean_ctor_get(v_range_1023_, 0);
v_end_1034_ = lean_ctor_get(v_range_1023_, 1);
v_line_1035_ = lean_ctor_get(v_start_1033_, 0);
v_character_1036_ = lean_ctor_get(v_start_1033_, 1);
v_line_1037_ = lean_ctor_get(v_end_1034_, 0);
v_character_1038_ = lean_ctor_get(v_end_1034_, 1);
v_val_1039_ = lean_ctor_get(v_parentDecl_x3f_1024_, 0);
lean_inc(v_val_1039_);
lean_inc(v_character_1038_);
lean_inc(v_line_1037_);
lean_inc(v_character_1036_);
lean_inc(v_line_1035_);
v___x_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1040_, 0, v_line_1035_);
lean_ctor_set(v___x_1040_, 1, v_character_1036_);
lean_ctor_set(v___x_1040_, 2, v_line_1037_);
lean_ctor_set(v___x_1040_, 3, v_character_1038_);
lean_ctor_set(v___x_1040_, 4, v_val_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1041_, lean_object* v_parentDecl_x3f_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1041_, v_parentDecl_x3f_1042_);
lean_dec(v_parentDecl_x3f_1042_);
lean_dec_ref(v_range_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1044_){
_start:
{
lean_object* v_startPosLine_1045_; lean_object* v_startPosCharacter_1046_; lean_object* v_endPosLine_1047_; lean_object* v_endPosCharacter_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_startPosLine_1045_ = lean_ctor_get(v_l_1044_, 0);
v_startPosCharacter_1046_ = lean_ctor_get(v_l_1044_, 1);
v_endPosLine_1047_ = lean_ctor_get(v_l_1044_, 2);
v_endPosCharacter_1048_ = lean_ctor_get(v_l_1044_, 3);
lean_inc(v_startPosCharacter_1046_);
lean_inc(v_startPosLine_1045_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_startPosLine_1045_);
lean_ctor_set(v___x_1049_, 1, v_startPosCharacter_1046_);
lean_inc(v_endPosCharacter_1048_);
lean_inc(v_endPosLine_1047_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_endPosLine_1047_);
lean_ctor_set(v___x_1050_, 1, v_endPosCharacter_1048_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1052_);
lean_dec_ref(v_l_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1054_){
_start:
{
lean_object* v_parentDecl_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_parentDecl_1055_ = lean_ctor_get(v_l_1054_, 4);
v___x_1056_ = lean_string_utf8_byte_size(v_parentDecl_1055_);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_nat_dec_eq(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_inc_ref(v_parentDecl_1055_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_parentDecl_1055_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1061_);
lean_dec_ref(v_l_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = l_Lean_JsonNumber_fromNat(v_n_1063_);
v___x_1065_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1066_, lean_object* v_l_1067_){
_start:
{
lean_object* v_startPosLine_1068_; lean_object* v_startPosCharacter_1069_; lean_object* v_endPosLine_1070_; lean_object* v_endPosCharacter_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_range_1077_; lean_object* v___x_1078_; 
v_startPosLine_1068_ = lean_ctor_get(v_l_1067_, 0);
v_startPosCharacter_1069_ = lean_ctor_get(v_l_1067_, 1);
v_endPosLine_1070_ = lean_ctor_get(v_l_1067_, 2);
v_endPosCharacter_1071_ = lean_ctor_get(v_l_1067_, 3);
v___x_1072_ = lean_box(0);
lean_inc(v_endPosCharacter_1071_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_endPosCharacter_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
lean_inc(v_endPosLine_1070_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_endPosLine_1070_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
lean_inc(v_startPosCharacter_1069_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_startPosCharacter_1069_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc(v_startPosLine_1068_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_startPosLine_1068_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v_range_1077_ = l_List_mapTR_loop___redArg(v___f_1066_, v___x_1076_, v___x_1072_);
v___x_1078_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_List_appendTR___redArg(v_range_1077_, v___x_1072_);
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
v_val_1080_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v___x_1078_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v___x_1078_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 3);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_val_1080_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1072_);
v___x_1087_ = l_List_appendTR___redArg(v_range_1077_, v___x_1086_);
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1090_, lean_object* v_l_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1090_, v_l_1091_);
lean_dec_ref(v_l_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_apply_1(v_locationToList_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1098_, lean_object* v___f_1099_, lean_object* v_locationToList_1100_, lean_object* v_i_1101_){
_start:
{
lean_object* v_definition_x3f_1102_; lean_object* v_usages_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1135_; 
v_definition_x3f_1102_ = lean_ctor_get(v_i_1101_, 0);
v_usages_1103_ = lean_ctor_get(v_i_1101_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_i_1101_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1105_ = v_i_1101_;
v_isShared_1106_ = v_isSharedCheck_1135_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_usages_1103_);
lean_inc(v_definition_x3f_1102_);
lean_dec(v_i_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1135_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___y_1109_; 
v___x_1107_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1102_) == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_locationToList_1100_);
v___x_1125_ = lean_box(0);
v___y_1109_ = v___x_1125_;
goto v___jp_1108_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_val_1126_ = lean_ctor_get(v_definition_x3f_1102_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_definition_x3f_1102_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v_definition_x3f_1102_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v_definition_x3f_1102_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = lean_apply_1(v_locationToList_1100_, v_val_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v___y_1109_ = v___x_1132_;
goto v___jp_1108_;
}
}
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_inc_ref(v___x_1098_);
v___x_1110_ = l_Lean_Option_toJson___redArg(v___x_1098_, v___y_1109_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1110_);
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1112_ = v___x_1105_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1113_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1114_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1115_ = lean_array_size(v_usages_1103_);
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1114_, v___f_1099_, v_sz_1115_, v___x_1116_, v_usages_1103_);
v___x_1118_ = l_Lean_Array_toJson___redArg(v___x_1098_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1113_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1112_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_Json_mkObj(v___x_1122_);
lean_dec_ref_known(v___x_1122_, 2);
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1232_; 
v___x_1151_ = lean_array_get_size(v_a_1150_);
v___x_1152_ = lean_unsigned_to_nat(4u);
v___x_1232_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(5u);
v___x_1234_ = lean_nat_dec_eq(v___x_1151_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1235_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1236_ = l_Nat_reprFast(v___x_1151_);
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
else
{
goto v___jp_1153_;
}
}
else
{
goto v___jp_1153_;
}
v___jp_1153_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_fget_borrowed(v_a_1150_, v___x_1154_);
lean_inc(v___x_1155_);
v___x_1156_ = l_Lean_Json_getNat_x3f(v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1165_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1166_ = lean_unsigned_to_nat(1u);
v___x_1167_ = lean_array_fget_borrowed(v_a_1150_, v___x_1166_);
lean_inc(v___x_1167_);
v___x_1168_ = l_Lean_Json_getNat_x3f(v___x_1167_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_1165_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1178_ = lean_unsigned_to_nat(2u);
v___x_1179_ = lean_array_fget_borrowed(v_a_1150_, v___x_1178_);
lean_inc(v___x_1179_);
v___x_1180_ = l_Lean_Json_getNat_x3f(v___x_1179_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1177_);
lean_dec(v_a_1165_);
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1189_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1190_ = lean_unsigned_to_nat(3u);
v___x_1191_ = lean_array_fget_borrowed(v_a_1150_, v___x_1190_);
lean_inc(v___x_1191_);
v___x_1192_ = l_Lean_Json_getNat_x3f(v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1189_);
lean_dec(v_a_1177_);
lean_dec(v_a_1165_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1231_; 
v_a_1201_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_unsigned_to_nat(5u);
v___x_1206_ = lean_nat_dec_eq(v___x_1151_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1165_);
lean_ctor_set(v___x_1208_, 1, v_a_1177_);
lean_ctor_set(v___x_1208_, 2, v_a_1189_);
lean_ctor_set(v___x_1208_, 3, v_a_1201_);
lean_ctor_set(v___x_1208_, 4, v___x_1207_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1208_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_del_object(v___x_1203_);
v___x_1212_ = lean_array_fget_borrowed(v_a_1150_, v___x_1152_);
lean_inc(v___x_1212_);
v___x_1213_ = l_Lean_Json_getStr_x3f(v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1201_);
lean_dec(v_a_1189_);
lean_dec(v_a_1177_);
lean_dec(v_a_1165_);
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
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
v_a_1222_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v___x_1213_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1213_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1165_);
lean_ctor_set(v___x_1226_, 1, v_a_1177_);
lean_ctor_set(v___x_1226_, 2, v_a_1189_);
lean_ctor_set(v___x_1226_, 3, v_a_1201_);
lean_ctor_set(v___x_1226_, 4, v_a_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1239_);
lean_dec_ref(v_a_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_toLocation_1244_, lean_object* v_j_1245_){
_start:
{
lean_object* v_definition_x3f_1247_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1245_);
v___x_1280_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1245_, v___x_1241_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_j_1245_);
lean_dec_ref(v_toLocation_1244_);
lean_dec_ref(v___x_1243_);
lean_dec_ref(v___x_1242_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; 
v_a_1289_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1280_, 1);
if (lean_obj_tag(v_a_1289_) == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_box(0);
v_definition_x3f_1247_ = v___x_1290_;
goto v___jp_1246_;
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1308_; 
v_val_1291_ = lean_ctor_get(v_a_1289_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1293_ = v_a_1289_;
v_isShared_1294_ = v_isSharedCheck_1308_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_a_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1308_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; 
lean_inc_ref(v_toLocation_1244_);
v___x_1295_ = lean_apply_1(v_toLocation_1244_, v_val_1291_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1293_);
lean_dec(v_j_1245_);
lean_dec_ref(v_toLocation_1244_);
lean_dec_ref(v___x_1243_);
lean_dec_ref(v___x_1242_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1295_, 1);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_a_1304_);
v___x_1306_ = v___x_1293_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
v_definition_x3f_1247_ = v___x_1306_;
goto v___jp_1246_;
}
}
}
}
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1249_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1245_, v___x_1242_, v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_definition_x3f_1247_);
lean_dec_ref(v_toLocation_1244_);
lean_dec_ref(v___x_1243_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1258_; size_t v_sz_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1258_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1249_, 1);
v_sz_1259_ = lean_array_size(v_a_1258_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1243_, v_toLocation_1244_, v_sz_1259_, v___x_1260_, v_a_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_definition_x3f_1247_);
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
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_a_1270_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1272_ = v___x_1261_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1261_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_definition_x3f_1247_);
lean_ctor_set(v___x_1274_, 1, v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
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
lean_object* v___x_1323_; 
v___x_1323_ = lean_box(1);
return v___x_1323_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_box(1);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1325_, lean_object* v_a_1326_, lean_object* v_b_1327_, lean_object* v_c_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_a_1326_);
lean_ctor_set(v___x_1329_, 1, v_b_1327_);
v___x_1330_ = lean_apply_2(v_f_1325_, v___x_1329_, v_c_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1331_, lean_object* v_____do__lift_1332_){
_start:
{
lean_object* v_a_1333_; lean_object* v___x_1334_; 
v_a_1333_ = lean_ctor_get(v_____do__lift_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref(v_____do__lift_1332_);
v___x_1334_ = lean_apply_2(v_toPure_1331_, lean_box(0), v_a_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_map_1337_, lean_object* v_init_1338_, lean_object* v_f_1339_){
_start:
{
lean_object* v_toApplicative_1340_; lean_object* v_toBind_1341_; lean_object* v_toPure_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; 
v_toApplicative_1340_ = lean_ctor_get(v_inst_1335_, 0);
v_toBind_1341_ = lean_ctor_get(v_inst_1335_, 1);
lean_inc(v_toBind_1341_);
v_toPure_1342_ = lean_ctor_get(v_toApplicative_1340_, 1);
lean_inc(v_toPure_1342_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1343_, 0, v_f_1339_);
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1335_, v___f_1343_, v_init_1338_, v_map_1337_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1345_, 0, v_toPure_1342_);
v___x_1346_ = lean_apply_4(v_toBind_1341_, lean_box(0), lean_box(0), v___x_1344_, v___f_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1347_){
_start:
{
lean_object* v___f_1348_; 
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1348_, 0, v_inst_1347_);
return v___f_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1349_, lean_object* v_inst_1350_){
_start:
{
lean_object* v___f_1351_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1351_, 0, v_inst_1350_);
return v___f_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v_startPosLine_1354_; lean_object* v_startPosCharacter_1355_; lean_object* v_endPosLine_1356_; lean_object* v_endPosCharacter_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_range_1363_; lean_object* v___x_1364_; 
v_startPosLine_1354_ = lean_ctor_get(v_x_1353_, 0);
v_startPosCharacter_1355_ = lean_ctor_get(v_x_1353_, 1);
v_endPosLine_1356_ = lean_ctor_get(v_x_1353_, 2);
v_endPosCharacter_1357_ = lean_ctor_get(v_x_1353_, 3);
v___x_1358_ = lean_box(0);
lean_inc(v_endPosCharacter_1357_);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_endPosCharacter_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_inc(v_endPosLine_1356_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_endPosLine_1356_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
lean_inc(v_startPosCharacter_1355_);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_startPosCharacter_1355_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_inc(v_startPosLine_1354_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_startPosLine_1354_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v_range_1363_ = l_List_mapTR_loop___redArg(v___f_1352_, v___x_1362_, v___x_1358_);
v___x_1364_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1353_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = l_List_appendTR___redArg(v_range_1363_, v___x_1358_);
return v___x_1365_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1375_; 
v_val_1366_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1368_ = v___x_1364_;
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v___x_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1375_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 3);
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1366_);
v___x_1371_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___x_1358_);
v___x_1373_ = l_List_appendTR___redArg(v_range_1363_, v___x_1372_);
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1376_, v_x_1377_);
lean_dec_ref(v_x_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1379_, lean_object* v___f_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v_snd_1382_; lean_object* v_fst_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1444_; 
v_snd_1382_ = lean_ctor_get(v_x_1381_, 1);
v_fst_1383_ = lean_ctor_get(v_x_1381_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_x_1381_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1385_ = v_x_1381_;
v_isShared_1386_ = v_isSharedCheck_1444_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_snd_1382_);
lean_inc(v_fst_1383_);
lean_dec(v_x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1444_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_definition_x3f_1387_; lean_object* v_usages_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1443_; 
v_definition_x3f_1387_ = lean_ctor_get(v_snd_1382_, 0);
v_usages_1388_ = lean_ctor_get(v_snd_1382_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_snd_1382_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1390_ = v_snd_1382_;
v_isShared_1391_ = v_isSharedCheck_1443_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_usages_1388_);
lean_inc(v_definition_x3f_1387_);
lean_dec(v_snd_1382_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1443_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___y_1397_; lean_object* v___y_1417_; 
v___x_1392_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1383_);
v___x_1393_ = l_Lean_Json_compress(v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1395_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1387_) == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v___f_1380_);
v___x_1419_ = lean_box(0);
v___y_1397_ = v___x_1419_;
goto v___jp_1396_;
}
else
{
lean_object* v_val_1420_; lean_object* v_startPosLine_1421_; lean_object* v_startPosCharacter_1422_; lean_object* v_endPosLine_1423_; lean_object* v_endPosCharacter_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_range_1430_; lean_object* v___x_1431_; 
v_val_1420_ = lean_ctor_get(v_definition_x3f_1387_, 0);
lean_inc(v_val_1420_);
lean_dec_ref_known(v_definition_x3f_1387_, 1);
v_startPosLine_1421_ = lean_ctor_get(v_val_1420_, 0);
v_startPosCharacter_1422_ = lean_ctor_get(v_val_1420_, 1);
v_endPosLine_1423_ = lean_ctor_get(v_val_1420_, 2);
v_endPosCharacter_1424_ = lean_ctor_get(v_val_1420_, 3);
v___x_1425_ = lean_box(0);
lean_inc(v_endPosCharacter_1424_);
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_endPosCharacter_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
lean_inc(v_endPosLine_1423_);
v___x_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_endPosLine_1423_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_inc(v_startPosCharacter_1422_);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_startPosCharacter_1422_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
lean_inc(v_startPosLine_1421_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_startPosLine_1421_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v_range_1430_ = l_List_mapTR_loop___redArg(v___f_1380_, v___x_1429_, v___x_1425_);
v___x_1431_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1420_);
lean_dec(v_val_1420_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = l_List_appendTR___redArg(v_range_1430_, v___x_1425_);
v___y_1417_ = v___x_1432_;
goto v___jp_1416_;
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v_val_1433_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v___x_1431_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v___x_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 3);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_val_1433_);
v___x_1438_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___x_1425_);
v___x_1440_ = l_List_appendTR___redArg(v_range_1430_, v___x_1439_);
v___y_1417_ = v___x_1440_;
goto v___jp_1416_;
}
}
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = l_Lean_Option_toJson___redArg(v___x_1394_, v___y_1397_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1398_);
lean_ctor_set(v___x_1385_, 0, v___x_1395_);
v___x_1400_ = v___x_1385_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; size_t v_sz_1403_; size_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1401_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1402_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1403_ = lean_array_size(v_usages_1388_);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1402_, v___f_1379_, v_sz_1403_, v___x_1404_, v_usages_1388_);
v___x_1406_ = l_Lean_Array_toJson___redArg(v___x_1394_, v___x_1405_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1406_);
lean_ctor_set(v___x_1390_, 0, v___x_1401_);
v___x_1408_ = v___x_1390_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1400_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_Json_mkObj(v___x_1411_);
lean_dec_ref_known(v___x_1411_, 2);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1393_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
return v___x_1413_;
}
}
}
v___jp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___y_1417_);
v___y_1397_ = v___x_1418_;
goto v___jp_1396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1445_, lean_object* v_x2_1446_, lean_object* v_x3_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_x1_1445_);
lean_ctor_set(v___x_1448_, 1, v_x2_1446_);
v___x_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_x3_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1450_, lean_object* v___f_1451_, lean_object* v_m_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1453_ = lean_box(0);
v___x_1454_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1454_, v___f_1450_, v___x_1453_, v_m_1452_);
v___x_1456_ = l_List_mapTR_loop___redArg(v___f_1451_, v___x_1455_, v___x_1453_);
v___x_1457_ = l_Lean_Json_mkObj(v___x_1456_);
lean_dec(v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1468_, lean_object* v_m_1469_, lean_object* v_k_1470_, lean_object* v_v_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Json_parse(v_k_1470_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
lean_dec_ref_known(v___x_1472_, 1);
v___x_1482_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1482_, 1);
v___x_1492_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__9));
v___x_1493_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1494_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1471_);
v___x_1495_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1471_, v___x_1493_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1625_; 
v_a_1504_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1506_ = v___x_1495_;
v_isShared_1507_ = v_isSharedCheck_1625_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1495_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1625_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v_definition_x3f_1510_; lean_object* v_a_1545_; 
v___x_1508_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1504_) == 0)
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1506_);
v___x_1547_ = lean_box(0);
v_definition_x3f_1510_ = v___x_1547_;
goto v___jp_1509_;
}
else
{
lean_object* v_val_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1616_; 
v_val_1548_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_a_1504_, 1);
v___x_1549_ = lean_array_get_size(v_val_1548_);
v___x_1550_ = lean_unsigned_to_nat(4u);
v___x_1616_ = lean_nat_dec_eq(v___x_1549_, v___x_1550_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = lean_unsigned_to_nat(5u);
v___x_1618_ = lean_nat_dec_eq(v___x_1549_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_dec(v_val_1548_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
v___x_1619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1620_ = l_Nat_reprFast(v___x_1549_);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
lean_dec_ref(v___x_1620_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1621_);
v___x_1623_ = v___x_1506_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_del_object(v___x_1506_);
goto v___jp_1551_;
}
}
else
{
lean_del_object(v___x_1506_);
goto v___jp_1551_;
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_array_fget_borrowed(v_val_1548_, v___x_1552_);
lean_inc(v___x_1553_);
v___x_1554_ = l_Lean_Json_getNat_x3f(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_val_1548_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
v___x_1565_ = lean_array_fget_borrowed(v_val_1548_, v___x_1564_);
lean_inc(v___x_1565_);
v___x_1566_ = l_Lean_Json_getNat_x3f(v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1563_);
lean_dec(v_val_1548_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
v___x_1577_ = lean_array_fget_borrowed(v_val_1548_, v___x_1576_);
lean_inc(v___x_1577_);
v___x_1578_ = l_Lean_Json_getNat_x3f(v___x_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_val_1548_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
v___x_1589_ = lean_array_fget_borrowed(v_val_1548_, v___x_1588_);
lean_inc(v___x_1589_);
v___x_1590_ = l_Lean_Json_getNat_x3f(v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_val_1548_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
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
lean_object* v_a_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1600_ = lean_unsigned_to_nat(5u);
v___x_1601_ = lean_nat_dec_eq(v___x_1549_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_val_1548_);
v___x_1602_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1603_, 0, v_a_1563_);
lean_ctor_set(v___x_1603_, 1, v_a_1575_);
lean_ctor_set(v___x_1603_, 2, v_a_1587_);
lean_ctor_set(v___x_1603_, 3, v_a_1599_);
lean_ctor_set(v___x_1603_, 4, v___x_1602_);
v_a_1545_ = v___x_1603_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_array_fget(v_val_1548_, v___x_1550_);
lean_dec(v_val_1548_);
v___x_1605_ = l_Lean_Json_getStr_x3f(v___x_1604_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1587_);
lean_dec(v_a_1575_);
lean_dec(v_a_1563_);
lean_dec(v_a_1491_);
lean_dec(v_v_1471_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1615_, 0, v_a_1563_);
lean_ctor_set(v___x_1615_, 1, v_a_1575_);
lean_ctor_set(v___x_1615_, 2, v_a_1587_);
lean_ctor_set(v___x_1615_, 3, v_a_1599_);
lean_ctor_set(v___x_1615_, 4, v_a_1614_);
v_a_1545_ = v___x_1615_;
goto v___jp_1544_;
}
}
}
}
}
}
}
}
v___jp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1512_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1471_, v___x_1508_, v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_definition_x3f_1510_);
lean_dec(v_a_1491_);
lean_dec(v_m_1469_);
lean_dec_ref(v_toLocation_1468_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v_a_1521_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1512_, 1);
v_sz_1522_ = lean_array_size(v_a_1521_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1492_, v_toLocation_1468_, v_sz_1522_, v___x_1523_, v_a_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_definition_x3f_1510_);
lean_dec(v_a_1491_);
lean_dec(v_m_1469_);
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
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1543_; 
v_a_1533_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1535_ = v___x_1524_;
v_isShared_1536_ = v_isSharedCheck_1543_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1524_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1543_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_definition_x3f_1510_);
lean_ctor_set(v___x_1537_, 1, v_a_1533_);
v___x_1538_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1539_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1538_, v_a_1491_, v___x_1537_, v_m_1469_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1539_);
v___x_1541_ = v___x_1535_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_a_1545_);
v_definition_x3f_1510_ = v___x_1546_;
goto v___jp_1509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1626_, lean_object* v___f_1627_, lean_object* v_j_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Json_getObj_x3f(v_j_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___f_1627_);
lean_dec_ref(v___x_1626_);
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
lean_dec_ref_known(v___x_1629_, 1);
v___x_1639_ = lean_box(1);
v___x_1640_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1626_, v___f_1627_, v___x_1639_, v_a_1638_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1647_, lean_object* v_k_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = l_Lean_Json_getObjValD(v_j_1647_, v_k_1648_);
v___x_1650_ = l_Lean_Json_getNat_x3f(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1651_, lean_object* v_k_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1651_, v_k_1652_);
lean_dec_ref(v_k_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1654_, lean_object* v_k_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = l_Lean_Json_getObjValD(v_j_1654_, v_k_1655_);
v___x_1657_ = l_Lean_Json_getBool_x3f(v___x_1656_);
lean_dec(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1658_, v_k_1659_);
lean_dec_ref(v_k_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_bs_1665_){
_start:
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_bs_1665_);
return v___x_1669_;
}
else
{
lean_object* v_v_1670_; 
v_v_1670_ = lean_array_uget_borrowed(v_bs_1665_, v_i_1664_);
if (lean_obj_tag(v_v_1670_) == 4)
{
lean_object* v_elems_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v_elems_1671_ = lean_ctor_get(v_v_1670_, 0);
v___x_1672_ = lean_array_get_size(v_elems_1671_);
v___x_1673_ = lean_unsigned_to_nat(4u);
v___x_1674_ = lean_nat_dec_eq(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_dec_ref(v_bs_1665_);
goto v___jp_1666_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = lean_array_fget_borrowed(v_elems_1671_, v___x_1675_);
lean_inc(v___x_1676_);
v___x_1677_ = l_Lean_Json_getStr_x3f(v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_bs_1665_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_a_1686_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_array_fget_borrowed(v_elems_1671_, v___x_1687_);
v___x_1689_ = l_Lean_Json_getBool_x3f(v___x_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_a_1686_);
lean_dec_ref(v_bs_1665_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
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
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_a_1698_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1699_ = lean_unsigned_to_nat(2u);
v___x_1700_ = lean_array_fget_borrowed(v_elems_1671_, v___x_1699_);
v___x_1701_ = l_Lean_Json_getBool_x3f(v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1698_);
lean_dec(v_a_1686_);
lean_dec_ref(v_bs_1665_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1710_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1711_ = lean_unsigned_to_nat(3u);
v___x_1712_ = lean_array_fget_borrowed(v_elems_1671_, v___x_1711_);
v___x_1713_ = l_Lean_Json_getBool_x3f(v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_a_1710_);
lean_dec(v_a_1698_);
lean_dec(v_a_1686_);
lean_dec_ref(v_bs_1665_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v_bs_x27_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v_a_1722_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1713_, 1);
v_bs_x27_1723_ = lean_array_uset(v_bs_1665_, v_i_1664_, v___x_1675_);
v___x_1724_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1724_, 0, v_a_1686_);
v___x_1725_ = lean_unbox(v_a_1698_);
lean_dec(v_a_1698_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1, v___x_1725_);
v___x_1726_ = lean_unbox(v_a_1710_);
lean_dec(v_a_1710_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1 + 1, v___x_1726_);
v___x_1727_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*1 + 2, v___x_1727_);
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1664_, v___x_1728_);
v___x_1730_ = lean_array_uset(v_bs_x27_1723_, v_i_1664_, v___x_1724_);
v_i_1664_ = v___x_1729_;
v_bs_1665_ = v___x_1730_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1665_);
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 4)
{
lean_object* v_elems_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v_elems_1741_ = lean_ctor_get(v_x_1740_, 0);
lean_inc_ref(v_elems_1741_);
lean_dec_ref_known(v_x_1740_, 1);
v_sz_1742_ = lean_array_size(v_elems_1741_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1742_, v___x_1743_, v_elems_1741_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1745_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1746_ = lean_unsigned_to_nat(80u);
v___x_1747_ = l_Lean_Json_pretty(v_x_1740_, v___x_1746_);
v___x_1748_ = lean_string_append(v___x_1745_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1752_, lean_object* v_k_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = l_Lean_Json_getObjValD(v_j_1752_, v_k_1753_);
v___x_1755_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1756_, lean_object* v_k_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1756_, v_k_1757_);
lean_dec_ref(v_k_1757_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = 1;
v___x_1768_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1769_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1768_, v___x_1767_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1772_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1773_ = lean_string_append(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = 1;
v___x_1777_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1777_, v___x_1776_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1780_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1781_ = lean_string_append(v___x_1780_, v___x_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1784_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1785_ = lean_string_append(v___x_1784_, v___x_1783_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = 1;
v___x_1790_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1794_ = lean_string_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1797_ = lean_string_append(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = 1;
v___x_1802_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1805_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1806_ = lean_string_append(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1808_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1809_ = lean_string_append(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1810_);
v___x_1812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1810_, v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1822_; 
lean_dec(v_json_1810_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1818_ = lean_string_append(v___x_1817_, v_a_1813_);
lean_dec(v_a_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_a_1823_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1810_);
v___x_1825_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1810_, v___x_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1823_);
lean_dec(v_json_1810_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1831_ = lean_string_append(v___x_1830_, v_a_1826_);
lean_dec(v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
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
v_a_1836_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1838_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1810_, v___x_1837_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1836_);
lean_dec(v_a_1823_);
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
v___x_1843_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
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
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1858_; 
v_a_1849_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1851_ = v___x_1838_;
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1838_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1856_; 
v___x_1853_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1853_, 0, v_a_1823_);
lean_ctor_set(v___x_1853_, 1, v_a_1849_);
v___x_1854_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*2, v___x_1854_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1853_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1861_, size_t v_i_1862_, lean_object* v_bs_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_lt(v_i_1862_, v_sz_1861_);
if (v___x_1864_ == 0)
{
return v_bs_1863_;
}
else
{
lean_object* v_v_1865_; lean_object* v_module_1866_; uint8_t v_isPrivate_1867_; uint8_t v_isAll_1868_; uint8_t v_isMeta_1869_; lean_object* v___x_1870_; lean_object* v_bs_x27_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v_v_1865_ = lean_array_uget_borrowed(v_bs_1863_, v_i_1862_);
v_module_1866_ = lean_ctor_get(v_v_1865_, 0);
lean_inc_ref(v_module_1866_);
v_isPrivate_1867_ = lean_ctor_get_uint8(v_v_1865_, sizeof(void*)*1);
v_isAll_1868_ = lean_ctor_get_uint8(v_v_1865_, sizeof(void*)*1 + 1);
v_isMeta_1869_ = lean_ctor_get_uint8(v_v_1865_, sizeof(void*)*1 + 2);
v___x_1870_ = lean_unsigned_to_nat(0u);
v_bs_x27_1871_ = lean_array_uset(v_bs_1863_, v_i_1862_, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_module_1866_);
v___x_1873_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1873_, 0, v_isPrivate_1867_);
v___x_1874_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1874_, 0, v_isAll_1868_);
v___x_1875_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1875_, 0, v_isMeta_1869_);
v___x_1876_ = lean_unsigned_to_nat(4u);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1876_);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1872_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1873_);
v___x_1880_ = lean_array_push(v___x_1879_, v___x_1874_);
v___x_1881_ = lean_array_push(v___x_1880_, v___x_1875_);
v___x_1882_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1862_, v___x_1883_);
v___x_1885_ = lean_array_uset(v_bs_x27_1871_, v_i_1862_, v___x_1882_);
v_i_1862_ = v___x_1884_;
v_bs_1863_ = v___x_1885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1887_, lean_object* v_i_1888_, lean_object* v_bs_1889_){
_start:
{
size_t v_sz_boxed_1890_; size_t v_i_boxed_1891_; lean_object* v_res_1892_; 
v_sz_boxed_1890_ = lean_unbox_usize(v_sz_1887_);
lean_dec(v_sz_1887_);
v_i_boxed_1891_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_res_1892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1890_, v_i_boxed_1891_, v_bs_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1893_){
_start:
{
size_t v_sz_1894_; size_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_sz_1894_ = lean_array_size(v_a_1893_);
v___x_1895_ = ((size_t)0ULL);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1894_, v___x_1895_, v_a_1893_);
v___x_1897_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
if (lean_obj_tag(v_a_1898_) == 0)
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_array_to_list(v_a_1899_);
return v___x_1900_;
}
else
{
lean_object* v_head_1901_; lean_object* v_tail_1902_; lean_object* v___x_1903_; 
v_head_1901_ = lean_ctor_get(v_a_1898_, 0);
lean_inc(v_head_1901_);
v_tail_1902_ = lean_ctor_get(v_a_1898_, 1);
lean_inc(v_tail_1902_);
lean_dec_ref_known(v_a_1898_, 2);
v___x_1903_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1899_, v_head_1901_);
v_a_1898_ = v_tail_1902_;
v_a_1899_ = v___x_1903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1907_){
_start:
{
lean_object* v_version_1908_; uint8_t v_isSetupFailure_1909_; lean_object* v_directImports_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_version_1908_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_version_1908_);
v_isSetupFailure_1909_ = lean_ctor_get_uint8(v_x_1907_, sizeof(void*)*2);
v_directImports_1910_ = lean_ctor_get(v_x_1907_, 1);
lean_inc_ref(v_directImports_1910_);
lean_dec_ref(v_x_1907_);
v___x_1911_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1912_ = l_Lean_JsonNumber_fromNat(v_version_1908_);
v___x_1913_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1911_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1918_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1918_, 0, v_isSetupFailure_1909_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1915_);
v___x_1921_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1922_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1910_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1915_);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___x_1915_);
v___x_1926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1920_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1916_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1929_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1927_, v___x_1928_);
v___x_1930_ = l_Lean_Json_mkObj(v___x_1929_);
lean_dec(v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1933_, lean_object* v_v_1934_, lean_object* v_t_1935_){
_start:
{
if (lean_obj_tag(v_t_1935_) == 0)
{
lean_object* v_size_1936_; lean_object* v_k_1937_; lean_object* v_v_1938_; lean_object* v_l_1939_; lean_object* v_r_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_2220_; 
v_size_1936_ = lean_ctor_get(v_t_1935_, 0);
v_k_1937_ = lean_ctor_get(v_t_1935_, 1);
v_v_1938_ = lean_ctor_get(v_t_1935_, 2);
v_l_1939_ = lean_ctor_get(v_t_1935_, 3);
v_r_1940_ = lean_ctor_get(v_t_1935_, 4);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_t_1935_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_1942_ = v_t_1935_;
v_isShared_1943_ = v_isSharedCheck_2220_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_r_1940_);
lean_inc(v_l_1939_);
lean_inc(v_v_1938_);
lean_inc(v_k_1937_);
lean_inc(v_size_1936_);
lean_dec(v_t_1935_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_2220_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_string_compare(v_k_1933_, v_k_1937_);
switch(v___x_1944_)
{
case 0:
{
lean_object* v_impl_1945_; lean_object* v___x_1946_; 
lean_dec(v_size_1936_);
v_impl_1945_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1933_, v_v_1934_, v_l_1939_);
v___x_1946_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1940_) == 0)
{
lean_object* v_size_1947_; lean_object* v_size_1948_; lean_object* v_k_1949_; lean_object* v_v_1950_; lean_object* v_l_1951_; lean_object* v_r_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v_size_1947_ = lean_ctor_get(v_r_1940_, 0);
v_size_1948_ = lean_ctor_get(v_impl_1945_, 0);
v_k_1949_ = lean_ctor_get(v_impl_1945_, 1);
v_v_1950_ = lean_ctor_get(v_impl_1945_, 2);
v_l_1951_ = lean_ctor_get(v_impl_1945_, 3);
v_r_1952_ = lean_ctor_get(v_impl_1945_, 4);
lean_inc(v_r_1952_);
v___x_1953_ = lean_unsigned_to_nat(3u);
v___x_1954_ = lean_nat_mul(v___x_1953_, v_size_1947_);
v___x_1955_ = lean_nat_dec_lt(v___x_1954_, v_size_1948_);
lean_dec(v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
lean_dec(v_r_1952_);
v___x_1956_ = lean_nat_add(v___x_1946_, v_size_1948_);
v___x_1957_ = lean_nat_add(v___x_1956_, v_size_1947_);
lean_dec(v___x_1956_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 3, v_impl_1945_);
lean_ctor_set(v___x_1942_, 0, v___x_1957_);
v___x_1959_ = v___x_1942_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_impl_1945_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_r_1940_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
else
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2026_; 
lean_inc(v_l_1951_);
lean_inc(v_v_1950_);
lean_inc(v_k_1949_);
lean_inc(v_size_1948_);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_impl_1945_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2027_ = lean_ctor_get(v_impl_1945_, 4);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_impl_1945_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_impl_1945_, 2);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_impl_1945_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_impl_1945_, 0);
lean_dec(v_unused_2031_);
v___x_1962_ = v_impl_1945_;
v_isShared_1963_ = v_isSharedCheck_2026_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v_impl_1945_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2026_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_size_1964_; lean_object* v_size_1965_; lean_object* v_k_1966_; lean_object* v_v_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_size_1964_ = lean_ctor_get(v_l_1951_, 0);
v_size_1965_ = lean_ctor_get(v_r_1952_, 0);
v_k_1966_ = lean_ctor_get(v_r_1952_, 1);
v_v_1967_ = lean_ctor_get(v_r_1952_, 2);
v_l_1968_ = lean_ctor_get(v_r_1952_, 3);
v_r_1969_ = lean_ctor_get(v_r_1952_, 4);
v___x_1970_ = lean_unsigned_to_nat(2u);
v___x_1971_ = lean_nat_mul(v___x_1970_, v_size_1964_);
v___x_1972_ = lean_nat_dec_lt(v_size_1965_, v___x_1971_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2001_; 
lean_inc(v_r_1969_);
lean_inc(v_l_1968_);
lean_inc(v_v_1967_);
lean_inc(v_k_1966_);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_r_1952_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2002_ = lean_ctor_get(v_r_1952_, 4);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_r_1952_, 3);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_r_1952_, 2);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_r_1952_, 1);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_r_1952_, 0);
lean_dec(v_unused_2006_);
v___x_1974_ = v_r_1952_;
v_isShared_1975_ = v_isSharedCheck_2001_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v_r_1952_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2001_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_1989_; lean_object* v___y_1991_; 
v___x_1976_ = lean_nat_add(v___x_1946_, v_size_1948_);
lean_dec(v_size_1948_);
v___x_1977_ = lean_nat_add(v___x_1976_, v_size_1947_);
lean_dec(v___x_1976_);
v___x_1989_ = lean_nat_add(v___x_1946_, v_size_1964_);
if (lean_obj_tag(v_l_1968_) == 0)
{
lean_object* v_size_1999_; 
v_size_1999_ = lean_ctor_get(v_l_1968_, 0);
lean_inc(v_size_1999_);
v___y_1991_ = v_size_1999_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_unsigned_to_nat(0u);
v___y_1991_ = v___x_2000_;
goto v___jp_1990_;
}
v___jp_1978_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_nat_add(v___y_1979_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec(v___y_1979_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 4, v_r_1940_);
lean_ctor_set(v___x_1974_, 3, v_r_1969_);
lean_ctor_set(v___x_1974_, 2, v_v_1938_);
lean_ctor_set(v___x_1974_, 1, v_k_1937_);
lean_ctor_set(v___x_1974_, 0, v___x_1982_);
v___x_1984_ = v___x_1974_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v_r_1969_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_r_1940_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v___x_1984_);
lean_ctor_set(v___x_1962_, 3, v___y_1980_);
lean_ctor_set(v___x_1962_, 2, v_v_1967_);
lean_ctor_set(v___x_1962_, 1, v_k_1966_);
lean_ctor_set(v___x_1962_, 0, v___x_1977_);
v___x_1986_ = v___x_1962_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___y_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
v___jp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_nat_add(v___x_1989_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec(v___x_1989_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_l_1968_);
lean_ctor_set(v___x_1942_, 3, v_l_1951_);
lean_ctor_set(v___x_1942_, 2, v_v_1950_);
lean_ctor_set(v___x_1942_, 1, v_k_1949_);
lean_ctor_set(v___x_1942_, 0, v___x_1992_);
v___x_1994_ = v___x_1942_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_k_1949_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_v_1950_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_l_1951_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v_l_1968_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_nat_add(v___x_1946_, v_size_1947_);
if (lean_obj_tag(v_r_1969_) == 0)
{
lean_object* v_size_1996_; 
v_size_1996_ = lean_ctor_get(v_r_1969_, 0);
lean_inc(v_size_1996_);
v___y_1979_ = v___x_1995_;
v___y_1980_ = v___x_1994_;
v___y_1981_ = v_size_1996_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v___y_1979_ = v___x_1995_;
v___y_1980_ = v___x_1994_;
v___y_1981_ = v___x_1997_;
goto v___jp_1978_;
}
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_del_object(v___x_1942_);
v___x_2007_ = lean_nat_add(v___x_1946_, v_size_1948_);
lean_dec(v_size_1948_);
v___x_2008_ = lean_nat_add(v___x_2007_, v_size_1947_);
lean_dec(v___x_2007_);
v___x_2009_ = lean_nat_add(v___x_1946_, v_size_1947_);
v___x_2010_ = lean_nat_add(v___x_2009_, v_size_1965_);
lean_dec(v___x_2009_);
lean_inc_ref(v_r_1940_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_r_1940_);
lean_ctor_set(v___x_1962_, 3, v_r_1952_);
lean_ctor_set(v___x_1962_, 2, v_v_1938_);
lean_ctor_set(v___x_1962_, 1, v_k_1937_);
lean_ctor_set(v___x_1962_, 0, v___x_2010_);
v___x_2012_ = v___x_1962_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_r_1952_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_r_1940_);
v___x_2012_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v_r_1940_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2020_ = lean_ctor_get(v_r_1940_, 4);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_r_1940_, 3);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_r_1940_, 2);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_r_1940_, 1);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_r_1940_, 0);
lean_dec(v_unused_2024_);
v___x_2014_ = v_r_1940_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_r_1940_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v___x_2012_);
lean_ctor_set(v___x_2014_, 3, v_l_1951_);
lean_ctor_set(v___x_2014_, 2, v_v_1950_);
lean_ctor_set(v___x_2014_, 1, v_k_1949_);
lean_ctor_set(v___x_2014_, 0, v___x_2008_);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1949_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_v_1950_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_l_1951_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v___x_2012_);
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
v_l_2032_ = lean_ctor_get(v_impl_1945_, 3);
if (lean_obj_tag(v_l_2032_) == 0)
{
lean_object* v_r_2033_; lean_object* v_k_2034_; lean_object* v_v_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2046_; 
lean_inc_ref(v_l_2032_);
v_r_2033_ = lean_ctor_get(v_impl_1945_, 4);
v_k_2034_ = lean_ctor_get(v_impl_1945_, 1);
v_v_2035_ = lean_ctor_get(v_impl_1945_, 2);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_impl_1945_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2047_ = lean_ctor_get(v_impl_1945_, 3);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_impl_1945_, 0);
lean_dec(v_unused_2048_);
v___x_2037_ = v_impl_1945_;
v_isShared_2038_ = v_isSharedCheck_2046_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_r_2033_);
lean_inc(v_v_2035_);
lean_inc(v_k_2034_);
lean_dec(v_impl_1945_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2046_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2039_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2033_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 3, v_r_2033_);
lean_ctor_set(v___x_2037_, 2, v_v_1938_);
lean_ctor_set(v___x_2037_, 1, v_k_1937_);
lean_ctor_set(v___x_2037_, 0, v___x_1946_);
v___x_2041_ = v___x_2037_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_r_2033_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_r_2033_);
v___x_2041_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_2041_);
lean_ctor_set(v___x_1942_, 3, v_l_2032_);
lean_ctor_set(v___x_1942_, 2, v_v_2035_);
lean_ctor_set(v___x_1942_, 1, v_k_2034_);
lean_ctor_set(v___x_1942_, 0, v___x_2039_);
v___x_2043_ = v___x_1942_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_2034_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_2035_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v___x_2041_);
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
else
{
lean_object* v_r_2049_; 
v_r_2049_ = lean_ctor_get(v_impl_1945_, 4);
lean_inc(v_r_2049_);
if (lean_obj_tag(v_r_2049_) == 0)
{
lean_object* v_k_2050_; lean_object* v_v_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2074_; 
lean_inc(v_l_2032_);
v_k_2050_ = lean_ctor_get(v_impl_1945_, 1);
v_v_2051_ = lean_ctor_get(v_impl_1945_, 2);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_impl_1945_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2075_ = lean_ctor_get(v_impl_1945_, 4);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_impl_1945_, 3);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1945_, 0);
lean_dec(v_unused_2077_);
v___x_2053_ = v_impl_1945_;
v_isShared_2054_ = v_isSharedCheck_2074_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_v_2051_);
lean_inc(v_k_2050_);
lean_dec(v_impl_1945_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2074_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_k_2055_; lean_object* v_v_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2070_; 
v_k_2055_ = lean_ctor_get(v_r_2049_, 1);
v_v_2056_ = lean_ctor_get(v_r_2049_, 2);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_r_2049_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; 
v_unused_2071_ = lean_ctor_get(v_r_2049_, 4);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_r_2049_, 3);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_r_2049_, 0);
lean_dec(v_unused_2073_);
v___x_2058_ = v_r_2049_;
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_v_2056_);
lean_inc(v_k_2055_);
lean_dec(v_r_2049_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2070_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_unsigned_to_nat(3u);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 4, v_l_2032_);
lean_ctor_set(v___x_2058_, 3, v_l_2032_);
lean_ctor_set(v___x_2058_, 2, v_v_2051_);
lean_ctor_set(v___x_2058_, 1, v_k_2050_);
lean_ctor_set(v___x_2058_, 0, v___x_1946_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_2050_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_2051_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_l_2032_);
v___x_2062_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 4, v_l_2032_);
lean_ctor_set(v___x_2053_, 2, v_v_1938_);
lean_ctor_set(v___x_2053_, 1, v_k_1937_);
lean_ctor_set(v___x_2053_, 0, v___x_1946_);
v___x_2064_ = v___x_2053_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_l_2032_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_2064_);
lean_ctor_set(v___x_1942_, 3, v___x_2062_);
lean_ctor_set(v___x_1942_, 2, v_v_2056_);
lean_ctor_set(v___x_1942_, 1, v_k_2055_);
lean_ctor_set(v___x_1942_, 0, v___x_2060_);
v___x_2066_ = v___x_1942_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2055_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2056_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_unsigned_to_nat(2u);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_r_2049_);
lean_ctor_set(v___x_1942_, 3, v_impl_1945_);
lean_ctor_set(v___x_1942_, 0, v___x_2078_);
v___x_2080_ = v___x_1942_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_impl_1945_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_r_2049_);
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
case 1:
{
lean_object* v___x_2083_; 
lean_dec(v_v_1938_);
lean_dec(v_k_1937_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 2, v_v_1934_);
lean_ctor_set(v___x_1942_, 1, v_k_1933_);
v___x_2083_ = v___x_1942_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_size_1936_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_1933_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_1934_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_l_1939_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_r_1940_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
default: 
{
lean_object* v_impl_2085_; lean_object* v___x_2086_; 
lean_dec(v_size_1936_);
v_impl_2085_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1933_, v_v_1934_, v_r_1940_);
v___x_2086_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1939_) == 0)
{
lean_object* v_size_2087_; lean_object* v_size_2088_; lean_object* v_k_2089_; lean_object* v_v_2090_; lean_object* v_l_2091_; lean_object* v_r_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_size_2087_ = lean_ctor_get(v_l_1939_, 0);
v_size_2088_ = lean_ctor_get(v_impl_2085_, 0);
v_k_2089_ = lean_ctor_get(v_impl_2085_, 1);
v_v_2090_ = lean_ctor_get(v_impl_2085_, 2);
v_l_2091_ = lean_ctor_get(v_impl_2085_, 3);
lean_inc(v_l_2091_);
v_r_2092_ = lean_ctor_get(v_impl_2085_, 4);
v___x_2093_ = lean_unsigned_to_nat(3u);
v___x_2094_ = lean_nat_mul(v___x_2093_, v_size_2087_);
v___x_2095_ = lean_nat_dec_lt(v___x_2094_, v_size_2088_);
lean_dec(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
lean_dec(v_l_2091_);
v___x_2096_ = lean_nat_add(v___x_2086_, v_size_2087_);
v___x_2097_ = lean_nat_add(v___x_2096_, v_size_2088_);
lean_dec(v___x_2096_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_impl_2085_);
lean_ctor_set(v___x_1942_, 0, v___x_2097_);
v___x_2099_ = v___x_1942_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_l_1939_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_impl_2085_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
else
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_r_2092_);
lean_inc(v_v_2090_);
lean_inc(v_k_2089_);
lean_inc(v_size_2088_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_impl_2085_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2165_ = lean_ctor_get(v_impl_2085_, 4);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_impl_2085_, 3);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_impl_2085_, 2);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_impl_2085_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_impl_2085_, 0);
lean_dec(v_unused_2169_);
v___x_2102_ = v_impl_2085_;
v_isShared_2103_ = v_isSharedCheck_2164_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_impl_2085_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2164_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_size_2104_; lean_object* v_k_2105_; lean_object* v_v_2106_; lean_object* v_l_2107_; lean_object* v_r_2108_; lean_object* v_size_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_size_2104_ = lean_ctor_get(v_l_2091_, 0);
v_k_2105_ = lean_ctor_get(v_l_2091_, 1);
v_v_2106_ = lean_ctor_get(v_l_2091_, 2);
v_l_2107_ = lean_ctor_get(v_l_2091_, 3);
v_r_2108_ = lean_ctor_get(v_l_2091_, 4);
v_size_2109_ = lean_ctor_get(v_r_2092_, 0);
v___x_2110_ = lean_unsigned_to_nat(2u);
v___x_2111_ = lean_nat_mul(v___x_2110_, v_size_2109_);
v___x_2112_ = lean_nat_dec_lt(v_size_2104_, v___x_2111_);
lean_dec(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2140_; 
lean_inc(v_r_2108_);
lean_inc(v_l_2107_);
lean_inc(v_v_2106_);
lean_inc(v_k_2105_);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_l_2091_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; lean_object* v_unused_2145_; 
v_unused_2141_ = lean_ctor_get(v_l_2091_, 4);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_l_2091_, 3);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_l_2091_, 2);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_l_2091_, 1);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_l_2091_, 0);
lean_dec(v_unused_2145_);
v___x_2114_ = v_l_2091_;
v_isShared_2115_ = v_isSharedCheck_2140_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v_l_2091_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2140_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2130_; 
v___x_2116_ = lean_nat_add(v___x_2086_, v_size_2087_);
v___x_2117_ = lean_nat_add(v___x_2116_, v_size_2088_);
lean_dec(v_size_2088_);
if (lean_obj_tag(v_l_2107_) == 0)
{
lean_object* v_size_2138_; 
v_size_2138_ = lean_ctor_get(v_l_2107_, 0);
lean_inc(v_size_2138_);
v___y_2130_ = v_size_2138_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v___y_2130_ = v___x_2139_;
goto v___jp_2129_;
}
v___jp_2118_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_nat_add(v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 4, v_r_2092_);
lean_ctor_set(v___x_2114_, 3, v_r_2108_);
lean_ctor_set(v___x_2114_, 2, v_v_2090_);
lean_ctor_set(v___x_2114_, 1, v_k_2089_);
lean_ctor_set(v___x_2114_, 0, v___x_2122_);
v___x_2124_ = v___x_2114_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_r_2108_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_r_2092_);
v___x_2124_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v___x_2124_);
lean_ctor_set(v___x_2102_, 3, v___y_2119_);
lean_ctor_set(v___x_2102_, 2, v_v_2106_);
lean_ctor_set(v___x_2102_, 1, v_k_2105_);
lean_ctor_set(v___x_2102_, 0, v___x_2117_);
v___x_2126_ = v___x_2102_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_k_2105_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_2106_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v___y_2119_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
v___jp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_nat_add(v___x_2116_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec(v___x_2116_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_l_2107_);
lean_ctor_set(v___x_1942_, 0, v___x_2131_);
v___x_2133_ = v___x_1942_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_l_1939_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v_l_2107_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_nat_add(v___x_2086_, v_size_2109_);
if (lean_obj_tag(v_r_2108_) == 0)
{
lean_object* v_size_2135_; 
v_size_2135_ = lean_ctor_get(v_r_2108_, 0);
lean_inc(v_size_2135_);
v___y_2119_ = v___x_2133_;
v___y_2120_ = v___x_2134_;
v___y_2121_ = v_size_2135_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___y_2119_ = v___x_2133_;
v___y_2120_ = v___x_2134_;
v___y_2121_ = v___x_2136_;
goto v___jp_2118_;
}
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_del_object(v___x_1942_);
v___x_2146_ = lean_nat_add(v___x_2086_, v_size_2087_);
v___x_2147_ = lean_nat_add(v___x_2146_, v_size_2088_);
lean_dec(v_size_2088_);
v___x_2148_ = lean_nat_add(v___x_2146_, v_size_2104_);
lean_dec(v___x_2146_);
lean_inc_ref(v_l_1939_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v_l_2091_);
lean_ctor_set(v___x_2102_, 3, v_l_1939_);
lean_ctor_set(v___x_2102_, 2, v_v_1938_);
lean_ctor_set(v___x_2102_, 1, v_k_1937_);
lean_ctor_set(v___x_2102_, 0, v___x_2148_);
v___x_2150_ = v___x_2102_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_1939_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_l_2091_);
v___x_2150_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_isSharedCheck_2157_ = !lean_is_exclusive(v_l_1939_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2158_ = lean_ctor_get(v_l_1939_, 4);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_l_1939_, 3);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_l_1939_, 2);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_l_1939_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_l_1939_, 0);
lean_dec(v_unused_2162_);
v___x_2152_ = v_l_1939_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v_l_1939_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v_r_2092_);
lean_ctor_set(v___x_2152_, 3, v___x_2150_);
lean_ctor_set(v___x_2152_, 2, v_v_2090_);
lean_ctor_set(v___x_2152_, 1, v_k_2089_);
lean_ctor_set(v___x_2152_, 0, v___x_2147_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2089_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2090_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_r_2092_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2170_; 
v_l_2170_ = lean_ctor_get(v_impl_2085_, 3);
lean_inc(v_l_2170_);
if (lean_obj_tag(v_l_2170_) == 0)
{
lean_object* v_r_2171_; lean_object* v_k_2172_; lean_object* v_v_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2196_; 
v_r_2171_ = lean_ctor_get(v_impl_2085_, 4);
v_k_2172_ = lean_ctor_get(v_impl_2085_, 1);
v_v_2173_ = lean_ctor_get(v_impl_2085_, 2);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_impl_2085_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; lean_object* v_unused_2198_; 
v_unused_2197_ = lean_ctor_get(v_impl_2085_, 3);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_impl_2085_, 0);
lean_dec(v_unused_2198_);
v___x_2175_ = v_impl_2085_;
v_isShared_2176_ = v_isSharedCheck_2196_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_r_2171_);
lean_inc(v_v_2173_);
lean_inc(v_k_2172_);
lean_dec(v_impl_2085_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2196_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_k_2177_; lean_object* v_v_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2192_; 
v_k_2177_ = lean_ctor_get(v_l_2170_, 1);
v_v_2178_ = lean_ctor_get(v_l_2170_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_l_2170_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2193_ = lean_ctor_get(v_l_2170_, 4);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_l_2170_, 3);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_l_2170_, 0);
lean_dec(v_unused_2195_);
v___x_2180_ = v_l_2170_;
v_isShared_2181_ = v_isSharedCheck_2192_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_v_2178_);
lean_inc(v_k_2177_);
lean_dec(v_l_2170_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2192_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2171_, 2);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 4, v_r_2171_);
lean_ctor_set(v___x_2180_, 3, v_r_2171_);
lean_ctor_set(v___x_2180_, 2, v_v_1938_);
lean_ctor_set(v___x_2180_, 1, v_k_1937_);
lean_ctor_set(v___x_2180_, 0, v___x_2086_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_r_2171_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_r_2171_);
v___x_2184_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
lean_inc(v_r_2171_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 3, v_r_2171_);
lean_ctor_set(v___x_2175_, 0, v___x_2086_);
v___x_2186_ = v___x_2175_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_k_2172_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_v_2173_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_r_2171_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v_r_2171_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_2186_);
lean_ctor_set(v___x_1942_, 3, v___x_2184_);
lean_ctor_set(v___x_1942_, 2, v_v_2178_);
lean_ctor_set(v___x_1942_, 1, v_k_2177_);
lean_ctor_set(v___x_1942_, 0, v___x_2182_);
v___x_2188_ = v___x_1942_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_k_2177_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_v_2178_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
else
{
lean_object* v_r_2199_; 
v_r_2199_ = lean_ctor_get(v_impl_2085_, 4);
lean_inc(v_r_2199_);
if (lean_obj_tag(v_r_2199_) == 0)
{
lean_object* v_k_2200_; lean_object* v_v_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2212_; 
v_k_2200_ = lean_ctor_get(v_impl_2085_, 1);
v_v_2201_ = lean_ctor_get(v_impl_2085_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_impl_2085_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2213_ = lean_ctor_get(v_impl_2085_, 4);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_impl_2085_, 3);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_impl_2085_, 0);
lean_dec(v_unused_2215_);
v___x_2203_ = v_impl_2085_;
v_isShared_2204_ = v_isSharedCheck_2212_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_v_2201_);
lean_inc(v_k_2200_);
lean_dec(v_impl_2085_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2212_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(3u);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v_l_2170_);
lean_ctor_set(v___x_2203_, 2, v_v_1938_);
lean_ctor_set(v___x_2203_, 1, v_k_1937_);
lean_ctor_set(v___x_2203_, 0, v___x_2086_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_2170_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_l_2170_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_r_2199_);
lean_ctor_set(v___x_1942_, 3, v___x_2207_);
lean_ctor_set(v___x_1942_, 2, v_v_2201_);
lean_ctor_set(v___x_1942_, 1, v_k_2200_);
lean_ctor_set(v___x_1942_, 0, v___x_2205_);
v___x_2209_ = v___x_1942_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2200_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2201_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_r_2199_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_unsigned_to_nat(2u);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_impl_2085_);
lean_ctor_set(v___x_1942_, 3, v_r_2199_);
lean_ctor_set(v___x_1942_, 0, v___x_2216_);
v___x_2218_ = v___x_1942_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_r_2199_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_impl_2085_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
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
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v_k_1933_);
lean_ctor_set(v___x_2222_, 2, v_v_1934_);
lean_ctor_set(v___x_2222_, 3, v_t_1935_);
lean_ctor_set(v___x_2222_, 4, v_t_1935_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_k_2225_; lean_object* v_v_2226_; lean_object* v_l_2227_; lean_object* v_r_2228_; lean_object* v___x_2229_; 
v_k_2225_ = lean_ctor_get(v_x_2224_, 1);
lean_inc(v_k_2225_);
v_v_2226_ = lean_ctor_get(v_x_2224_, 2);
lean_inc(v_v_2226_);
v_l_2227_ = lean_ctor_get(v_x_2224_, 3);
lean_inc(v_l_2227_);
v_r_2228_ = lean_ctor_get(v_x_2224_, 4);
lean_inc(v_r_2228_);
lean_dec_ref_known(v_x_2224_, 5);
v___x_2229_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2223_, v_l_2227_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_dec(v_r_2228_);
lean_dec(v_v_2226_);
lean_dec(v_k_2225_);
return v___x_2229_;
}
else
{
if (lean_obj_tag(v_v_2226_) == 4)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2344_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2344_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2344_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_elems_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_elems_2234_ = lean_ctor_get(v_v_2226_, 0);
lean_inc_ref(v_elems_2234_);
lean_dec_ref_known(v_v_2226_, 1);
v___x_2235_ = lean_array_get_size(v_elems_2234_);
v___x_2236_ = lean_unsigned_to_nat(8u);
v___x_2237_ = lean_nat_dec_eq(v___x_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v___x_2238_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2239_ = l_Nat_reprFast(v___x_2235_);
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
lean_dec_ref(v___x_2239_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2240_);
v___x_2242_ = v___x_2232_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_del_object(v___x_2232_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2245_);
lean_inc(v___x_2246_);
v___x_2247_ = l_Lean_Json_getNat_x3f(v___x_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_a_2256_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2247_, 1);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2257_);
lean_inc(v___x_2258_);
v___x_2259_ = l_Lean_Json_getNat_x3f(v___x_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_a_2268_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2269_ = lean_unsigned_to_nat(2u);
v___x_2270_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2269_);
lean_inc(v___x_2270_);
v___x_2271_ = l_Lean_Json_getNat_x3f(v___x_2270_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_a_2280_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2281_ = lean_unsigned_to_nat(3u);
v___x_2282_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2281_);
lean_inc(v___x_2282_);
v___x_2283_ = l_Lean_Json_getNat_x3f(v___x_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_a_2280_);
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_a_2292_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2293_ = lean_unsigned_to_nat(4u);
v___x_2294_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2293_);
lean_inc(v___x_2294_);
v___x_2295_ = l_Lean_Json_getNat_x3f(v___x_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_a_2304_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2305_ = lean_unsigned_to_nat(5u);
v___x_2306_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2305_);
lean_inc(v___x_2306_);
v___x_2307_ = l_Lean_Json_getNat_x3f(v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2307_, 1);
v___x_2317_ = lean_unsigned_to_nat(6u);
v___x_2318_ = lean_array_get_borrowed(v___x_2244_, v_elems_2234_, v___x_2317_);
lean_inc(v___x_2318_);
v___x_2319_ = l_Lean_Json_getNat_x3f(v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec_ref(v_elems_2234_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2328_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2329_ = lean_unsigned_to_nat(7u);
v___x_2330_ = lean_array_get(v___x_2244_, v_elems_2234_, v___x_2329_);
lean_dec_ref(v_elems_2234_);
v___x_2331_ = l_Lean_Json_getNat_x3f(v___x_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2328_);
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec(v_a_2268_);
lean_dec(v_a_2256_);
lean_dec(v_a_2230_);
lean_dec(v_r_2228_);
lean_dec(v_k_2225_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2341_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2341_, 0, v_a_2256_);
lean_ctor_set(v___x_2341_, 1, v_a_2268_);
lean_ctor_set(v___x_2341_, 2, v_a_2280_);
lean_ctor_set(v___x_2341_, 3, v_a_2292_);
lean_ctor_set(v___x_2341_, 4, v_a_2304_);
lean_ctor_set(v___x_2341_, 5, v_a_2316_);
lean_ctor_set(v___x_2341_, 6, v_a_2328_);
lean_ctor_set(v___x_2341_, 7, v_a_2340_);
v___x_2342_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2225_, v___x_2341_, v_a_2230_);
v_init_2223_ = v___x_2342_;
v_x_2224_ = v_r_2228_;
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
lean_object* v___x_2345_; 
lean_dec_ref_known(v___x_2229_, 1);
lean_dec(v_r_2228_);
lean_dec(v_v_2226_);
lean_dec(v_k_2225_);
v___x_2345_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2345_;
}
}
}
else
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_init_2223_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2347_, lean_object* v_k_2348_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = l_Lean_Json_getObjValD(v_j_2347_, v_k_2348_);
v___x_2350_ = l_Lean_Json_getObj_x3f(v___x_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2360_ = lean_box(1);
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2360_, v_a_2359_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2362_, lean_object* v_k_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2362_, v_k_2363_);
lean_dec_ref(v_k_2363_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2365_, size_t v_i_2366_, lean_object* v_bs_2367_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2366_, v_sz_2365_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_bs_2367_);
return v___x_2369_;
}
else
{
lean_object* v_v_2370_; lean_object* v___x_2371_; lean_object* v_bs_x27_2372_; size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v_v_2370_ = lean_array_uget(v_bs_2367_, v_i_2366_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v_bs_x27_2372_ = lean_array_uset(v_bs_2367_, v_i_2366_, v___x_2371_);
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_add(v_i_2366_, v___x_2373_);
v___x_2375_ = lean_array_uset(v_bs_x27_2372_, v_i_2366_, v_v_2370_);
v_i_2366_ = v___x_2374_;
v_bs_2367_ = v___x_2375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2377_, lean_object* v_i_2378_, lean_object* v_bs_2379_){
_start:
{
size_t v_sz_boxed_2380_; size_t v_i_boxed_2381_; lean_object* v_res_2382_; 
v_sz_boxed_2380_ = lean_unbox_usize(v_sz_2377_);
lean_dec(v_sz_2377_);
v_i_boxed_2381_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_res_2382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2380_, v_i_boxed_2381_, v_bs_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 4)
{
lean_object* v_elems_2384_; size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v_elems_2384_ = lean_ctor_get(v_x_2383_, 0);
lean_inc_ref(v_elems_2384_);
lean_dec_ref_known(v_x_2383_, 1);
v_sz_2385_ = lean_array_size(v_elems_2384_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2385_, v___x_2386_, v_elems_2384_);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2388_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2389_ = lean_unsigned_to_nat(80u);
v___x_2390_ = l_Lean_Json_pretty(v_x_2383_, v___x_2389_);
v___x_2391_ = lean_string_append(v___x_2388_, v___x_2390_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2393_ = lean_string_append(v___x_2391_, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2397_){
_start:
{
if (lean_obj_tag(v_x_2397_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2397_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2416_; 
v_a_2408_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2410_ = v___x_2399_;
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_a_2408_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2417_, lean_object* v_k_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = l_Lean_Json_getObjValD(v_j_2417_, v_k_2418_);
v___x_2420_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2421_, lean_object* v_k_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2421_, v_k_2422_);
lean_dec_ref(v_k_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2424_, lean_object* v_v_2425_, lean_object* v_t_2426_){
_start:
{
if (lean_obj_tag(v_t_2426_) == 0)
{
lean_object* v_size_2427_; lean_object* v_k_2428_; lean_object* v_v_2429_; lean_object* v_l_2430_; lean_object* v_r_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2711_; 
v_size_2427_ = lean_ctor_get(v_t_2426_, 0);
v_k_2428_ = lean_ctor_get(v_t_2426_, 1);
v_v_2429_ = lean_ctor_get(v_t_2426_, 2);
v_l_2430_ = lean_ctor_get(v_t_2426_, 3);
v_r_2431_ = lean_ctor_get(v_t_2426_, 4);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_t_2426_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2433_ = v_t_2426_;
v_isShared_2434_ = v_isSharedCheck_2711_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_r_2431_);
lean_inc(v_l_2430_);
lean_inc(v_v_2429_);
lean_inc(v_k_2428_);
lean_inc(v_size_2427_);
lean_dec(v_t_2426_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2711_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
uint8_t v___x_2435_; 
v___x_2435_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2424_, v_k_2428_);
switch(v___x_2435_)
{
case 0:
{
lean_object* v_impl_2436_; lean_object* v___x_2437_; 
lean_dec(v_size_2427_);
v_impl_2436_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2424_, v_v_2425_, v_l_2430_);
v___x_2437_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2431_) == 0)
{
lean_object* v_size_2438_; lean_object* v_size_2439_; lean_object* v_k_2440_; lean_object* v_v_2441_; lean_object* v_l_2442_; lean_object* v_r_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v_size_2438_ = lean_ctor_get(v_r_2431_, 0);
v_size_2439_ = lean_ctor_get(v_impl_2436_, 0);
v_k_2440_ = lean_ctor_get(v_impl_2436_, 1);
v_v_2441_ = lean_ctor_get(v_impl_2436_, 2);
v_l_2442_ = lean_ctor_get(v_impl_2436_, 3);
v_r_2443_ = lean_ctor_get(v_impl_2436_, 4);
lean_inc(v_r_2443_);
v___x_2444_ = lean_unsigned_to_nat(3u);
v___x_2445_ = lean_nat_mul(v___x_2444_, v_size_2438_);
v___x_2446_ = lean_nat_dec_lt(v___x_2445_, v_size_2439_);
lean_dec(v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
lean_dec(v_r_2443_);
v___x_2447_ = lean_nat_add(v___x_2437_, v_size_2439_);
v___x_2448_ = lean_nat_add(v___x_2447_, v_size_2438_);
lean_dec(v___x_2447_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 3, v_impl_2436_);
lean_ctor_set(v___x_2433_, 0, v___x_2448_);
v___x_2450_ = v___x_2433_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_impl_2436_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_r_2431_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
else
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2517_; 
lean_inc(v_l_2442_);
lean_inc(v_v_2441_);
lean_inc(v_k_2440_);
lean_inc(v_size_2439_);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_impl_2436_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; lean_object* v_unused_2522_; 
v_unused_2518_ = lean_ctor_get(v_impl_2436_, 4);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_impl_2436_, 3);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_impl_2436_, 2);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_impl_2436_, 1);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_impl_2436_, 0);
lean_dec(v_unused_2522_);
v___x_2453_ = v_impl_2436_;
v_isShared_2454_ = v_isSharedCheck_2517_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v_impl_2436_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2517_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_size_2455_; lean_object* v_size_2456_; lean_object* v_k_2457_; lean_object* v_v_2458_; lean_object* v_l_2459_; lean_object* v_r_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_size_2455_ = lean_ctor_get(v_l_2442_, 0);
v_size_2456_ = lean_ctor_get(v_r_2443_, 0);
v_k_2457_ = lean_ctor_get(v_r_2443_, 1);
v_v_2458_ = lean_ctor_get(v_r_2443_, 2);
v_l_2459_ = lean_ctor_get(v_r_2443_, 3);
v_r_2460_ = lean_ctor_get(v_r_2443_, 4);
v___x_2461_ = lean_unsigned_to_nat(2u);
v___x_2462_ = lean_nat_mul(v___x_2461_, v_size_2455_);
v___x_2463_ = lean_nat_dec_lt(v_size_2456_, v___x_2462_);
lean_dec(v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2492_; 
lean_inc(v_r_2460_);
lean_inc(v_l_2459_);
lean_inc(v_v_2458_);
lean_inc(v_k_2457_);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_r_2443_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; lean_object* v_unused_2497_; 
v_unused_2493_ = lean_ctor_get(v_r_2443_, 4);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_r_2443_, 3);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_r_2443_, 2);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_r_2443_, 1);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_r_2443_, 0);
lean_dec(v_unused_2497_);
v___x_2465_ = v_r_2443_;
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v_r_2443_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2492_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___x_2480_; lean_object* v___y_2482_; 
v___x_2467_ = lean_nat_add(v___x_2437_, v_size_2439_);
lean_dec(v_size_2439_);
v___x_2468_ = lean_nat_add(v___x_2467_, v_size_2438_);
lean_dec(v___x_2467_);
v___x_2480_ = lean_nat_add(v___x_2437_, v_size_2455_);
if (lean_obj_tag(v_l_2459_) == 0)
{
lean_object* v_size_2490_; 
v_size_2490_ = lean_ctor_get(v_l_2459_, 0);
lean_inc(v_size_2490_);
v___y_2482_ = v_size_2490_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_unsigned_to_nat(0u);
v___y_2482_ = v___x_2491_;
goto v___jp_2481_;
}
v___jp_2469_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_nat_add(v___y_2470_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec(v___y_2470_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 4, v_r_2431_);
lean_ctor_set(v___x_2465_, 3, v_r_2460_);
lean_ctor_set(v___x_2465_, 2, v_v_2429_);
lean_ctor_set(v___x_2465_, 1, v_k_2428_);
lean_ctor_set(v___x_2465_, 0, v___x_2473_);
v___x_2475_ = v___x_2465_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_r_2460_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v_r_2431_);
v___x_2475_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2477_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v___x_2475_);
lean_ctor_set(v___x_2453_, 3, v___y_2471_);
lean_ctor_set(v___x_2453_, 2, v_v_2458_);
lean_ctor_set(v___x_2453_, 1, v_k_2457_);
lean_ctor_set(v___x_2453_, 0, v___x_2468_);
v___x_2477_ = v___x_2453_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_k_2457_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_v_2458_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v___y_2471_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
v___jp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_nat_add(v___x_2480_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec(v___x_2480_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_l_2459_);
lean_ctor_set(v___x_2433_, 3, v_l_2442_);
lean_ctor_set(v___x_2433_, 2, v_v_2441_);
lean_ctor_set(v___x_2433_, 1, v_k_2440_);
lean_ctor_set(v___x_2433_, 0, v___x_2483_);
v___x_2485_ = v___x_2433_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_k_2440_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_v_2441_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_l_2442_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_l_2459_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_nat_add(v___x_2437_, v_size_2438_);
if (lean_obj_tag(v_r_2460_) == 0)
{
lean_object* v_size_2487_; 
v_size_2487_ = lean_ctor_get(v_r_2460_, 0);
lean_inc(v_size_2487_);
v___y_2470_ = v___x_2486_;
v___y_2471_ = v___x_2485_;
v___y_2472_ = v_size_2487_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___y_2470_ = v___x_2486_;
v___y_2471_ = v___x_2485_;
v___y_2472_ = v___x_2488_;
goto v___jp_2469_;
}
}
}
}
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
lean_del_object(v___x_2433_);
v___x_2498_ = lean_nat_add(v___x_2437_, v_size_2439_);
lean_dec(v_size_2439_);
v___x_2499_ = lean_nat_add(v___x_2498_, v_size_2438_);
lean_dec(v___x_2498_);
v___x_2500_ = lean_nat_add(v___x_2437_, v_size_2438_);
v___x_2501_ = lean_nat_add(v___x_2500_, v_size_2456_);
lean_dec(v___x_2500_);
lean_inc_ref(v_r_2431_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v_r_2431_);
lean_ctor_set(v___x_2453_, 3, v_r_2443_);
lean_ctor_set(v___x_2453_, 2, v_v_2429_);
lean_ctor_set(v___x_2453_, 1, v_k_2428_);
lean_ctor_set(v___x_2453_, 0, v___x_2501_);
v___x_2503_ = v___x_2453_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_r_2443_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_r_2431_);
v___x_2503_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_isSharedCheck_2510_ = !lean_is_exclusive(v_r_2431_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; 
v_unused_2511_ = lean_ctor_get(v_r_2431_, 4);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_r_2431_, 3);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_r_2431_, 2);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_r_2431_, 1);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_r_2431_, 0);
lean_dec(v_unused_2515_);
v___x_2505_ = v_r_2431_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_dec(v_r_2431_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 4, v___x_2503_);
lean_ctor_set(v___x_2505_, 3, v_l_2442_);
lean_ctor_set(v___x_2505_, 2, v_v_2441_);
lean_ctor_set(v___x_2505_, 1, v_k_2440_);
lean_ctor_set(v___x_2505_, 0, v___x_2499_);
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2440_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2441_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_l_2442_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v___x_2503_);
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
v_l_2523_ = lean_ctor_get(v_impl_2436_, 3);
if (lean_obj_tag(v_l_2523_) == 0)
{
lean_object* v_r_2524_; lean_object* v_k_2525_; lean_object* v_v_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2537_; 
lean_inc_ref(v_l_2523_);
v_r_2524_ = lean_ctor_get(v_impl_2436_, 4);
v_k_2525_ = lean_ctor_get(v_impl_2436_, 1);
v_v_2526_ = lean_ctor_get(v_impl_2436_, 2);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_impl_2436_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; lean_object* v_unused_2539_; 
v_unused_2538_ = lean_ctor_get(v_impl_2436_, 3);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_impl_2436_, 0);
lean_dec(v_unused_2539_);
v___x_2528_ = v_impl_2436_;
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_r_2524_);
lean_inc(v_v_2526_);
lean_inc(v_k_2525_);
lean_dec(v_impl_2436_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2524_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 3, v_r_2524_);
lean_ctor_set(v___x_2528_, 2, v_v_2429_);
lean_ctor_set(v___x_2528_, 1, v_k_2428_);
lean_ctor_set(v___x_2528_, 0, v___x_2437_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_r_2524_);
v___x_2532_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v___x_2532_);
lean_ctor_set(v___x_2433_, 3, v_l_2523_);
lean_ctor_set(v___x_2433_, 2, v_v_2526_);
lean_ctor_set(v___x_2433_, 1, v_k_2525_);
lean_ctor_set(v___x_2433_, 0, v___x_2530_);
v___x_2534_ = v___x_2433_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2525_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2526_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v___x_2532_);
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
else
{
lean_object* v_r_2540_; 
v_r_2540_ = lean_ctor_get(v_impl_2436_, 4);
lean_inc(v_r_2540_);
if (lean_obj_tag(v_r_2540_) == 0)
{
lean_object* v_k_2541_; lean_object* v_v_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2565_; 
lean_inc(v_l_2523_);
v_k_2541_ = lean_ctor_get(v_impl_2436_, 1);
v_v_2542_ = lean_ctor_get(v_impl_2436_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_impl_2436_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2566_ = lean_ctor_get(v_impl_2436_, 4);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_impl_2436_, 3);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_impl_2436_, 0);
lean_dec(v_unused_2568_);
v___x_2544_ = v_impl_2436_;
v_isShared_2545_ = v_isSharedCheck_2565_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_v_2542_);
lean_inc(v_k_2541_);
lean_dec(v_impl_2436_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2565_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_k_2546_; lean_object* v_v_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2561_; 
v_k_2546_ = lean_ctor_get(v_r_2540_, 1);
v_v_2547_ = lean_ctor_get(v_r_2540_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_r_2540_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; 
v_unused_2562_ = lean_ctor_get(v_r_2540_, 4);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_r_2540_, 3);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_r_2540_, 0);
lean_dec(v_unused_2564_);
v___x_2549_ = v_r_2540_;
v_isShared_2550_ = v_isSharedCheck_2561_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_v_2547_);
lean_inc(v_k_2546_);
lean_dec(v_r_2540_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2561_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_unsigned_to_nat(3u);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 4, v_l_2523_);
lean_ctor_set(v___x_2549_, 3, v_l_2523_);
lean_ctor_set(v___x_2549_, 2, v_v_2542_);
lean_ctor_set(v___x_2549_, 1, v_k_2541_);
lean_ctor_set(v___x_2549_, 0, v___x_2437_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v_l_2523_);
v___x_2553_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2555_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 4, v_l_2523_);
lean_ctor_set(v___x_2544_, 2, v_v_2429_);
lean_ctor_set(v___x_2544_, 1, v_k_2428_);
lean_ctor_set(v___x_2544_, 0, v___x_2437_);
v___x_2555_ = v___x_2544_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_l_2523_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v___x_2555_);
lean_ctor_set(v___x_2433_, 3, v___x_2553_);
lean_ctor_set(v___x_2433_, 2, v_v_2547_);
lean_ctor_set(v___x_2433_, 1, v_k_2546_);
lean_ctor_set(v___x_2433_, 0, v___x_2551_);
v___x_2557_ = v___x_2433_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_2546_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_2547_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(2u);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_r_2540_);
lean_ctor_set(v___x_2433_, 3, v_impl_2436_);
lean_ctor_set(v___x_2433_, 0, v___x_2569_);
v___x_2571_ = v___x_2433_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_impl_2436_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_r_2540_);
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
case 1:
{
lean_object* v___x_2574_; 
lean_dec(v_v_2429_);
lean_dec(v_k_2428_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v_v_2425_);
lean_ctor_set(v___x_2433_, 1, v_k_2424_);
v___x_2574_ = v___x_2433_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_size_2427_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_k_2424_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_v_2425_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_l_2430_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_r_2431_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
default: 
{
lean_object* v_impl_2576_; lean_object* v___x_2577_; 
lean_dec(v_size_2427_);
v_impl_2576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2424_, v_v_2425_, v_r_2431_);
v___x_2577_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2430_) == 0)
{
lean_object* v_size_2578_; lean_object* v_size_2579_; lean_object* v_k_2580_; lean_object* v_v_2581_; lean_object* v_l_2582_; lean_object* v_r_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_size_2578_ = lean_ctor_get(v_l_2430_, 0);
v_size_2579_ = lean_ctor_get(v_impl_2576_, 0);
v_k_2580_ = lean_ctor_get(v_impl_2576_, 1);
v_v_2581_ = lean_ctor_get(v_impl_2576_, 2);
v_l_2582_ = lean_ctor_get(v_impl_2576_, 3);
lean_inc(v_l_2582_);
v_r_2583_ = lean_ctor_get(v_impl_2576_, 4);
v___x_2584_ = lean_unsigned_to_nat(3u);
v___x_2585_ = lean_nat_mul(v___x_2584_, v_size_2578_);
v___x_2586_ = lean_nat_dec_lt(v___x_2585_, v_size_2579_);
lean_dec(v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec(v_l_2582_);
v___x_2587_ = lean_nat_add(v___x_2577_, v_size_2578_);
v___x_2588_ = lean_nat_add(v___x_2587_, v_size_2579_);
lean_dec(v___x_2587_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_impl_2576_);
lean_ctor_set(v___x_2433_, 0, v___x_2588_);
v___x_2590_ = v___x_2433_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_l_2430_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_impl_2576_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2655_; 
lean_inc(v_r_2583_);
lean_inc(v_v_2581_);
lean_inc(v_k_2580_);
lean_inc(v_size_2579_);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_impl_2576_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; 
v_unused_2656_ = lean_ctor_get(v_impl_2576_, 4);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_impl_2576_, 3);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_impl_2576_, 2);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_impl_2576_, 1);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_impl_2576_, 0);
lean_dec(v_unused_2660_);
v___x_2593_ = v_impl_2576_;
v_isShared_2594_ = v_isSharedCheck_2655_;
goto v_resetjp_2592_;
}
else
{
lean_dec(v_impl_2576_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2655_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_size_2595_; lean_object* v_k_2596_; lean_object* v_v_2597_; lean_object* v_l_2598_; lean_object* v_r_2599_; lean_object* v_size_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v_size_2595_ = lean_ctor_get(v_l_2582_, 0);
v_k_2596_ = lean_ctor_get(v_l_2582_, 1);
v_v_2597_ = lean_ctor_get(v_l_2582_, 2);
v_l_2598_ = lean_ctor_get(v_l_2582_, 3);
v_r_2599_ = lean_ctor_get(v_l_2582_, 4);
v_size_2600_ = lean_ctor_get(v_r_2583_, 0);
v___x_2601_ = lean_unsigned_to_nat(2u);
v___x_2602_ = lean_nat_mul(v___x_2601_, v_size_2600_);
v___x_2603_ = lean_nat_dec_lt(v_size_2595_, v___x_2602_);
lean_dec(v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2631_; 
lean_inc(v_r_2599_);
lean_inc(v_l_2598_);
lean_inc(v_v_2597_);
lean_inc(v_k_2596_);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_l_2582_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2632_ = lean_ctor_get(v_l_2582_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2582_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2582_, 2);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_l_2582_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_l_2582_, 0);
lean_dec(v_unused_2636_);
v___x_2605_ = v_l_2582_;
v_isShared_2606_ = v_isSharedCheck_2631_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v_l_2582_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2631_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2621_; 
v___x_2607_ = lean_nat_add(v___x_2577_, v_size_2578_);
v___x_2608_ = lean_nat_add(v___x_2607_, v_size_2579_);
lean_dec(v_size_2579_);
if (lean_obj_tag(v_l_2598_) == 0)
{
lean_object* v_size_2629_; 
v_size_2629_ = lean_ctor_get(v_l_2598_, 0);
lean_inc(v_size_2629_);
v___y_2621_ = v_size_2629_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_unsigned_to_nat(0u);
v___y_2621_ = v___x_2630_;
goto v___jp_2620_;
}
v___jp_2609_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = lean_nat_add(v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec(v___y_2611_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 4, v_r_2583_);
lean_ctor_set(v___x_2605_, 3, v_r_2599_);
lean_ctor_set(v___x_2605_, 2, v_v_2581_);
lean_ctor_set(v___x_2605_, 1, v_k_2580_);
lean_ctor_set(v___x_2605_, 0, v___x_2613_);
v___x_2615_ = v___x_2605_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_r_2599_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_r_2583_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 4, v___x_2615_);
lean_ctor_set(v___x_2593_, 3, v___y_2610_);
lean_ctor_set(v___x_2593_, 2, v_v_2597_);
lean_ctor_set(v___x_2593_, 1, v_k_2596_);
lean_ctor_set(v___x_2593_, 0, v___x_2608_);
v___x_2617_ = v___x_2593_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_k_2596_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_v_2597_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v___y_2610_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_nat_add(v___x_2607_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec(v___x_2607_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_l_2598_);
lean_ctor_set(v___x_2433_, 0, v___x_2622_);
v___x_2624_ = v___x_2433_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v_l_2430_);
lean_ctor_set(v_reuseFailAlloc_2628_, 4, v_l_2598_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_nat_add(v___x_2577_, v_size_2600_);
if (lean_obj_tag(v_r_2599_) == 0)
{
lean_object* v_size_2626_; 
v_size_2626_ = lean_ctor_get(v_r_2599_, 0);
lean_inc(v_size_2626_);
v___y_2610_ = v___x_2624_;
v___y_2611_ = v___x_2625_;
v___y_2612_ = v_size_2626_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_unsigned_to_nat(0u);
v___y_2610_ = v___x_2624_;
v___y_2611_ = v___x_2625_;
v___y_2612_ = v___x_2627_;
goto v___jp_2609_;
}
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
lean_del_object(v___x_2433_);
v___x_2637_ = lean_nat_add(v___x_2577_, v_size_2578_);
v___x_2638_ = lean_nat_add(v___x_2637_, v_size_2579_);
lean_dec(v_size_2579_);
v___x_2639_ = lean_nat_add(v___x_2637_, v_size_2595_);
lean_dec(v___x_2637_);
lean_inc_ref(v_l_2430_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 4, v_l_2582_);
lean_ctor_set(v___x_2593_, 3, v_l_2430_);
lean_ctor_set(v___x_2593_, 2, v_v_2429_);
lean_ctor_set(v___x_2593_, 1, v_k_2428_);
lean_ctor_set(v___x_2593_, 0, v___x_2639_);
v___x_2641_ = v___x_2593_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_l_2430_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_l_2582_);
v___x_2641_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_isSharedCheck_2648_ = !lean_is_exclusive(v_l_2430_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; lean_object* v_unused_2650_; lean_object* v_unused_2651_; lean_object* v_unused_2652_; lean_object* v_unused_2653_; 
v_unused_2649_ = lean_ctor_get(v_l_2430_, 4);
lean_dec(v_unused_2649_);
v_unused_2650_ = lean_ctor_get(v_l_2430_, 3);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_l_2430_, 2);
lean_dec(v_unused_2651_);
v_unused_2652_ = lean_ctor_get(v_l_2430_, 1);
lean_dec(v_unused_2652_);
v_unused_2653_ = lean_ctor_get(v_l_2430_, 0);
lean_dec(v_unused_2653_);
v___x_2643_ = v_l_2430_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v_l_2430_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 4, v_r_2583_);
lean_ctor_set(v___x_2643_, 3, v___x_2641_);
lean_ctor_set(v___x_2643_, 2, v_v_2581_);
lean_ctor_set(v___x_2643_, 1, v_k_2580_);
lean_ctor_set(v___x_2643_, 0, v___x_2638_);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2580_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2581_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v_r_2583_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2661_; 
v_l_2661_ = lean_ctor_get(v_impl_2576_, 3);
lean_inc(v_l_2661_);
if (lean_obj_tag(v_l_2661_) == 0)
{
lean_object* v_r_2662_; lean_object* v_k_2663_; lean_object* v_v_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2687_; 
v_r_2662_ = lean_ctor_get(v_impl_2576_, 4);
v_k_2663_ = lean_ctor_get(v_impl_2576_, 1);
v_v_2664_ = lean_ctor_get(v_impl_2576_, 2);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_impl_2576_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; lean_object* v_unused_2689_; 
v_unused_2688_ = lean_ctor_get(v_impl_2576_, 3);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_impl_2576_, 0);
lean_dec(v_unused_2689_);
v___x_2666_ = v_impl_2576_;
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_r_2662_);
lean_inc(v_v_2664_);
lean_inc(v_k_2663_);
lean_dec(v_impl_2576_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2683_; 
v_k_2668_ = lean_ctor_get(v_l_2661_, 1);
v_v_2669_ = lean_ctor_get(v_l_2661_, 2);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_l_2661_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; lean_object* v_unused_2685_; lean_object* v_unused_2686_; 
v_unused_2684_ = lean_ctor_get(v_l_2661_, 4);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v_l_2661_, 3);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_l_2661_, 0);
lean_dec(v_unused_2686_);
v___x_2671_ = v_l_2661_;
v_isShared_2672_ = v_isSharedCheck_2683_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
lean_dec(v_l_2661_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2683_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2662_, 2);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 4, v_r_2662_);
lean_ctor_set(v___x_2671_, 3, v_r_2662_);
lean_ctor_set(v___x_2671_, 2, v_v_2429_);
lean_ctor_set(v___x_2671_, 1, v_k_2428_);
lean_ctor_set(v___x_2671_, 0, v___x_2577_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_r_2662_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_r_2662_);
v___x_2675_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
lean_inc(v_r_2662_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 3, v_r_2662_);
lean_ctor_set(v___x_2666_, 0, v___x_2577_);
v___x_2677_ = v___x_2666_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_k_2663_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v_v_2664_);
lean_ctor_set(v_reuseFailAlloc_2681_, 3, v_r_2662_);
lean_ctor_set(v_reuseFailAlloc_2681_, 4, v_r_2662_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v___x_2677_);
lean_ctor_set(v___x_2433_, 3, v___x_2675_);
lean_ctor_set(v___x_2433_, 2, v_v_2669_);
lean_ctor_set(v___x_2433_, 1, v_k_2668_);
lean_ctor_set(v___x_2433_, 0, v___x_2673_);
v___x_2679_ = v___x_2433_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_k_2668_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_v_2669_);
lean_ctor_set(v_reuseFailAlloc_2680_, 3, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2680_, 4, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
else
{
lean_object* v_r_2690_; 
v_r_2690_ = lean_ctor_get(v_impl_2576_, 4);
lean_inc(v_r_2690_);
if (lean_obj_tag(v_r_2690_) == 0)
{
lean_object* v_k_2691_; lean_object* v_v_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2703_; 
v_k_2691_ = lean_ctor_get(v_impl_2576_, 1);
v_v_2692_ = lean_ctor_get(v_impl_2576_, 2);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_impl_2576_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2704_ = lean_ctor_get(v_impl_2576_, 4);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_impl_2576_, 3);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_impl_2576_, 0);
lean_dec(v_unused_2706_);
v___x_2694_ = v_impl_2576_;
v_isShared_2695_ = v_isSharedCheck_2703_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_v_2692_);
lean_inc(v_k_2691_);
lean_dec(v_impl_2576_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2703_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_unsigned_to_nat(3u);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v_l_2661_);
lean_ctor_set(v___x_2694_, 2, v_v_2429_);
lean_ctor_set(v___x_2694_, 1, v_k_2428_);
lean_ctor_set(v___x_2694_, 0, v___x_2577_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_l_2661_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_l_2661_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_r_2690_);
lean_ctor_set(v___x_2433_, 3, v___x_2698_);
lean_ctor_set(v___x_2433_, 2, v_v_2692_);
lean_ctor_set(v___x_2433_, 1, v_k_2691_);
lean_ctor_set(v___x_2433_, 0, v___x_2696_);
v___x_2700_ = v___x_2433_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_k_2691_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_v_2692_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_r_2690_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_unsigned_to_nat(2u);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_impl_2576_);
lean_ctor_set(v___x_2433_, 3, v_r_2690_);
lean_ctor_set(v___x_2433_, 0, v___x_2707_);
v___x_2709_ = v___x_2433_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2428_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2429_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_r_2690_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_impl_2576_);
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
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v_k_2424_);
lean_ctor_set(v___x_2713_, 2, v_v_2425_);
lean_ctor_set(v___x_2713_, 3, v_t_2426_);
lean_ctor_set(v___x_2713_, 4, v_t_2426_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2714_, size_t v_i_2715_, lean_object* v_bs_2716_){
_start:
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_usize_dec_lt(v_i_2715_, v_sz_2714_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_bs_2716_);
return v___x_2718_;
}
else
{
lean_object* v_v_2719_; lean_object* v___x_2720_; lean_object* v_bs_x27_2721_; lean_object* v_a_2723_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2794_; 
v_v_2719_ = lean_array_uget(v_bs_2716_, v_i_2715_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v_bs_x27_2721_ = lean_array_uset(v_bs_2716_, v_i_2715_, v___x_2720_);
v___x_2728_ = lean_array_get_size(v_v_2719_);
v___x_2729_ = lean_unsigned_to_nat(4u);
v___x_2794_ = lean_nat_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = lean_unsigned_to_nat(5u);
v___x_2796_ = lean_nat_dec_eq(v___x_2728_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec_ref(v_bs_x27_2721_);
lean_dec(v_v_2719_);
v___x_2797_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2798_ = l_Nat_reprFast(v___x_2728_);
v___x_2799_ = lean_string_append(v___x_2797_, v___x_2798_);
lean_dec_ref(v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
else
{
goto v___jp_2730_;
}
}
else
{
goto v___jp_2730_;
}
v___jp_2722_:
{
size_t v___x_2724_; size_t v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = ((size_t)1ULL);
v___x_2725_ = lean_usize_add(v_i_2715_, v___x_2724_);
v___x_2726_ = lean_array_uset(v_bs_x27_2721_, v_i_2715_, v_a_2723_);
v_i_2715_ = v___x_2725_;
v_bs_2716_ = v___x_2726_;
goto _start;
}
v___jp_2730_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_array_fget_borrowed(v_v_2719_, v___x_2720_);
lean_inc(v___x_2731_);
v___x_2732_ = l_Lean_Json_getNat_x3f(v___x_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v_bs_x27_2721_);
lean_dec(v_v_2719_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_a_2741_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_array_fget_borrowed(v_v_2719_, v___x_2742_);
lean_inc(v___x_2743_);
v___x_2744_ = l_Lean_Json_getNat_x3f(v___x_2743_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2741_);
lean_dec_ref(v_bs_x27_2721_);
lean_dec(v_v_2719_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_a_2753_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2754_ = lean_unsigned_to_nat(2u);
v___x_2755_ = lean_array_fget_borrowed(v_v_2719_, v___x_2754_);
lean_inc(v___x_2755_);
v___x_2756_ = l_Lean_Json_getNat_x3f(v___x_2755_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2753_);
lean_dec(v_a_2741_);
lean_dec_ref(v_bs_x27_2721_);
lean_dec(v_v_2719_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_a_2765_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2766_ = lean_unsigned_to_nat(3u);
v___x_2767_ = lean_array_fget_borrowed(v_v_2719_, v___x_2766_);
lean_inc(v___x_2767_);
v___x_2768_ = l_Lean_Json_getNat_x3f(v___x_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2753_);
lean_dec(v_a_2741_);
lean_dec_ref(v_bs_x27_2721_);
lean_dec(v_v_2719_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_a_2777_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2778_ = lean_unsigned_to_nat(5u);
v___x_2779_ = lean_nat_dec_eq(v___x_2728_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v_v_2719_);
v___x_2780_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2741_);
lean_ctor_set(v___x_2781_, 1, v_a_2753_);
lean_ctor_set(v___x_2781_, 2, v_a_2765_);
lean_ctor_set(v___x_2781_, 3, v_a_2777_);
lean_ctor_set(v___x_2781_, 4, v___x_2780_);
v_a_2723_ = v___x_2781_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_array_fget(v_v_2719_, v___x_2729_);
lean_dec(v_v_2719_);
v___x_2783_ = l_Lean_Json_getStr_x3f(v___x_2782_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2777_);
lean_dec(v_a_2765_);
lean_dec(v_a_2753_);
lean_dec(v_a_2741_);
lean_dec_ref(v_bs_x27_2721_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2793_, 0, v_a_2741_);
lean_ctor_set(v___x_2793_, 1, v_a_2753_);
lean_ctor_set(v___x_2793_, 2, v_a_2765_);
lean_ctor_set(v___x_2793_, 3, v_a_2777_);
lean_ctor_set(v___x_2793_, 4, v_a_2792_);
v_a_2723_ = v___x_2793_;
goto v___jp_2722_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2801_, lean_object* v_i_2802_, lean_object* v_bs_2803_){
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2801_);
lean_dec(v_sz_2801_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2804_, v_i_boxed_2805_, v_bs_2803_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2807_, size_t v_i_2808_, lean_object* v_bs_2809_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2808_, v_sz_2807_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_bs_2809_);
return v___x_2811_;
}
else
{
lean_object* v_v_2812_; lean_object* v___x_2813_; 
v_v_2812_ = lean_array_uget_borrowed(v_bs_2809_, v_i_2808_);
lean_inc(v_v_2812_);
v___x_2813_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v_bs_2809_);
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
lean_object* v_a_2822_; lean_object* v___x_2823_; lean_object* v_bs_x27_2824_; size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v_a_2822_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2823_ = lean_unsigned_to_nat(0u);
v_bs_x27_2824_ = lean_array_uset(v_bs_2809_, v_i_2808_, v___x_2823_);
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_add(v_i_2808_, v___x_2825_);
v___x_2827_ = lean_array_uset(v_bs_x27_2824_, v_i_2808_, v_a_2822_);
v_i_2808_ = v___x_2826_;
v_bs_2809_ = v___x_2827_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2829_, lean_object* v_i_2830_, lean_object* v_bs_2831_){
_start:
{
size_t v_sz_boxed_2832_; size_t v_i_boxed_2833_; lean_object* v_res_2834_; 
v_sz_boxed_2832_ = lean_unbox_usize(v_sz_2829_);
lean_dec(v_sz_2829_);
v_i_boxed_2833_ = lean_unbox_usize(v_i_2830_);
lean_dec(v_i_2830_);
v_res_2834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2832_, v_i_boxed_2833_, v_bs_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2835_){
_start:
{
if (lean_obj_tag(v_x_2835_) == 4)
{
lean_object* v_elems_2836_; size_t v_sz_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v_elems_2836_ = lean_ctor_get(v_x_2835_, 0);
lean_inc_ref(v_elems_2836_);
lean_dec_ref_known(v_x_2835_, 1);
v_sz_2837_ = lean_array_size(v_elems_2836_);
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2837_, v___x_2838_, v_elems_2836_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2840_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2841_ = lean_unsigned_to_nat(80u);
v___x_2842_ = l_Lean_Json_pretty(v_x_2835_, v___x_2841_);
v___x_2843_ = lean_string_append(v___x_2840_, v___x_2842_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2847_, lean_object* v_k_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = l_Lean_Json_getObjValD(v_j_2847_, v_k_2848_);
v___x_2850_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2851_, lean_object* v_k_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2851_, v_k_2852_);
lean_dec_ref(v_k_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2854_, lean_object* v_x_2855_){
_start:
{
if (lean_obj_tag(v_x_2855_) == 0)
{
lean_object* v_k_2856_; lean_object* v_v_2857_; lean_object* v_l_2858_; lean_object* v_r_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3019_; 
v_k_2856_ = lean_ctor_get(v_x_2855_, 1);
v_v_2857_ = lean_ctor_get(v_x_2855_, 2);
v_l_2858_ = lean_ctor_get(v_x_2855_, 3);
v_r_2859_ = lean_ctor_get(v_x_2855_, 4);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v_x_2855_, 0);
lean_dec(v_unused_3020_);
v___x_2861_ = v_x_2855_;
v_isShared_2862_ = v_isSharedCheck_3019_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_r_2859_);
lean_inc(v_l_2858_);
lean_inc(v_v_2857_);
lean_inc(v_k_2856_);
lean_dec(v_x_2855_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3019_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2854_, v_l_2858_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
lean_dec(v_k_2856_);
return v___x_2863_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_3018_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_3018_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_3018_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_Json_parse(v_k_2856_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2878_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2877_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v_definition_x3f_2889_; lean_object* v_a_2917_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_a_2887_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2921_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2857_);
v___x_2922_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2857_, v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
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
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3017_; 
v_a_2931_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2933_ = v___x_2922_;
v_isShared_2934_ = v_isSharedCheck_3017_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2922_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3017_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
if (lean_obj_tag(v_a_2931_) == 0)
{
lean_object* v___x_2935_; 
lean_del_object(v___x_2933_);
lean_del_object(v___x_2866_);
lean_del_object(v___x_2861_);
v___x_2935_ = lean_box(0);
v_definition_x3f_2889_ = v___x_2935_;
goto v___jp_2888_;
}
else
{
lean_object* v_val_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_3008_; 
v_val_2936_ = lean_ctor_get(v_a_2931_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v_a_2931_, 1);
v___x_2937_ = lean_array_get_size(v_val_2936_);
v___x_2938_ = lean_unsigned_to_nat(4u);
v___x_3008_ = lean_nat_dec_eq(v___x_2937_, v___x_2938_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_unsigned_to_nat(5u);
v___x_3010_ = lean_nat_dec_eq(v___x_2937_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
lean_dec(v_val_2936_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v___x_3011_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3012_ = l_Nat_reprFast(v___x_2937_);
v___x_3013_ = lean_string_append(v___x_3011_, v___x_3012_);
lean_dec_ref(v___x_3012_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 0);
lean_ctor_set(v___x_2933_, 0, v___x_3013_);
v___x_3015_ = v___x_2933_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
else
{
lean_del_object(v___x_2933_);
goto v___jp_2939_;
}
}
else
{
lean_del_object(v___x_2933_);
goto v___jp_2939_;
}
v___jp_2939_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_array_fget_borrowed(v_val_2936_, v___x_2940_);
lean_inc(v___x_2941_);
v___x_2942_ = l_Lean_Json_getNat_x3f(v___x_2941_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_val_2936_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2951_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2952_ = lean_unsigned_to_nat(1u);
v___x_2953_ = lean_array_fget_borrowed(v_val_2936_, v___x_2952_);
lean_inc(v___x_2953_);
v___x_2954_ = l_Lean_Json_getNat_x3f(v___x_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2951_);
lean_dec(v_val_2936_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
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
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2963_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2964_ = lean_unsigned_to_nat(2u);
v___x_2965_ = lean_array_fget_borrowed(v_val_2936_, v___x_2964_);
lean_inc(v___x_2965_);
v___x_2966_ = l_Lean_Json_getNat_x3f(v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2963_);
lean_dec(v_a_2951_);
lean_dec(v_val_2936_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2975_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2976_ = lean_unsigned_to_nat(3u);
v___x_2977_ = lean_array_fget_borrowed(v_val_2936_, v___x_2976_);
lean_inc(v___x_2977_);
v___x_2978_ = l_Lean_Json_getNat_x3f(v___x_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_a_2975_);
lean_dec(v_a_2963_);
lean_dec(v_a_2951_);
lean_dec(v_val_2936_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_a_2987_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2988_ = lean_unsigned_to_nat(5u);
v___x_2989_ = lean_nat_dec_eq(v___x_2937_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_dec(v_val_2936_);
v___x_2990_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 4, v___x_2990_);
lean_ctor_set(v___x_2861_, 3, v_a_2987_);
lean_ctor_set(v___x_2861_, 2, v_a_2975_);
lean_ctor_set(v___x_2861_, 1, v_a_2963_);
lean_ctor_set(v___x_2861_, 0, v_a_2951_);
v___x_2992_ = v___x_2861_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2951_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_a_2963_);
lean_ctor_set(v_reuseFailAlloc_2993_, 2, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_2993_, 3, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 4, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
v_a_2917_ = v___x_2992_;
goto v___jp_2916_;
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_array_fget(v_val_2936_, v___x_2938_);
lean_dec(v_val_2936_);
v___x_2995_ = l_Lean_Json_getStr_x3f(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2987_);
lean_dec(v_a_2975_);
lean_dec(v_a_2963_);
lean_dec(v_a_2951_);
lean_dec(v_a_2887_);
lean_del_object(v___x_2866_);
lean_dec(v_a_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_r_2859_);
lean_dec(v_v_2857_);
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
lean_object* v_a_3004_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_2995_, 1);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 4, v_a_3004_);
lean_ctor_set(v___x_2861_, 3, v_a_2987_);
lean_ctor_set(v___x_2861_, 2, v_a_2975_);
lean_ctor_set(v___x_2861_, 1, v_a_2963_);
lean_ctor_set(v___x_2861_, 0, v_a_2951_);
v___x_3006_ = v___x_2861_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_2951_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_a_2963_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_3007_, 4, v_a_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
v_a_2917_ = v___x_3006_;
goto v___jp_2916_;
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
v___jp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2891_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2857_, v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_definition_x3f_2889_);
lean_dec(v_a_2887_);
lean_dec(v_a_2864_);
lean_dec(v_r_2859_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_object* v_a_2900_; size_t v_sz_2901_; size_t v___x_2902_; lean_object* v___x_2903_; 
v_a_2900_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2891_, 1);
v_sz_2901_ = lean_array_size(v_a_2900_);
v___x_2902_ = ((size_t)0ULL);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2901_, v___x_2902_, v_a_2900_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_definition_x3f_2889_);
lean_dec(v_a_2887_);
lean_dec(v_a_2864_);
lean_dec(v_r_2859_);
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_a_2912_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_definition_x3f_2889_);
lean_ctor_set(v___x_2913_, 1, v_a_2912_);
v___x_2914_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2887_, v___x_2913_, v_a_2864_);
v_init_2854_ = v___x_2914_;
v_x_2855_ = v_r_2859_;
goto _start;
}
}
}
v___jp_2916_:
{
lean_object* v___x_2919_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_a_2917_);
v___x_2919_ = v___x_2866_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
v_definition_x3f_2889_ = v___x_2919_;
goto v___jp_2888_;
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
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_init_2854_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3022_, lean_object* v_k_3023_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = l_Lean_Json_getObjValD(v_j_3022_, v_k_3023_);
v___x_3025_ = l_Lean_Json_getObj_x3f(v___x_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3034_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3035_ = lean_box(1);
v___x_3036_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3035_, v_a_3034_);
return v___x_3036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3037_, lean_object* v_k_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3037_, v_k_3038_);
lean_dec_ref(v_k_3038_);
return v_res_3039_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = 1;
v___x_3046_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3049_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3050_ = lean_string_append(v___x_3049_, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3052_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3053_ = lean_string_append(v___x_3052_, v___x_3051_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3055_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3056_ = lean_string_append(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = 1;
v___x_3061_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3062_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3064_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3065_ = lean_string_append(v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3067_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3068_ = lean_string_append(v___x_3067_, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = 1;
v___x_3073_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3076_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3077_ = lean_string_append(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3079_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3081_){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3081_);
v___x_3083_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3081_, v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_json_3081_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3093_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3093_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3088_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3089_ = lean_string_append(v___x_3088_, v_a_3084_);
lean_dec(v_a_3084_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3089_);
v___x_3091_ = v___x_3086_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3094_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3095_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3081_);
v___x_3096_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3081_, v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_a_3094_);
lean_dec(v_json_3081_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3102_ = lean_string_append(v___x_3101_, v_a_3097_);
lean_dec(v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3107_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3081_, v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3094_);
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
v___x_3114_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
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
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3128_; 
v_a_3120_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3122_ = v___x_3109_;
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3109_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3094_);
lean_ctor_set(v___x_3124_, 1, v_a_3107_);
lean_ctor_set(v___x_3124_, 2, v_a_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3129_, lean_object* v_k_3130_, lean_object* v_v_3131_, lean_object* v_t_3132_, lean_object* v_hl_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3130_, v_v_3131_, v_t_3132_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3135_, lean_object* v_k_3136_, lean_object* v_v_3137_, lean_object* v_t_3138_, lean_object* v_hl_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3136_, v_v_3137_, v_t_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3143_, lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
lean_object* v_k_3145_; lean_object* v_v_3146_; lean_object* v_l_3147_; lean_object* v_r_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_k_3145_ = lean_ctor_get(v_x_3144_, 1);
v_v_3146_ = lean_ctor_get(v_x_3144_, 2);
v_l_3147_ = lean_ctor_get(v_x_3144_, 3);
v_r_3148_ = lean_ctor_get(v_x_3144_, 4);
v___x_3149_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3143_, v_r_3148_);
lean_inc(v_v_3146_);
lean_inc(v_k_3145_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_k_3145_);
lean_ctor_set(v___x_3150_, 1, v_v_3146_);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3149_);
v_init_3143_ = v___x_3151_;
v_x_3144_ = v_l_3147_;
goto _start;
}
else
{
return v_init_3143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3153_, v_x_3154_);
lean_dec(v_x_3154_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3156_, size_t v_i_3157_, lean_object* v_bs_3158_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = lean_usize_dec_lt(v_i_3157_, v_sz_3156_);
if (v___x_3159_ == 0)
{
return v_bs_3158_;
}
else
{
lean_object* v_v_3160_; lean_object* v___x_3161_; lean_object* v_bs_x27_3162_; size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
v_v_3160_ = lean_array_uget(v_bs_3158_, v_i_3157_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v_bs_x27_3162_ = lean_array_uset(v_bs_3158_, v_i_3157_, v___x_3161_);
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3157_, v___x_3163_);
v___x_3165_ = lean_array_uset(v_bs_x27_3162_, v_i_3157_, v_v_3160_);
v_i_3157_ = v___x_3164_;
v_bs_3158_ = v___x_3165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3167_, lean_object* v_i_3168_, lean_object* v_bs_3169_){
_start:
{
size_t v_sz_boxed_3170_; size_t v_i_boxed_3171_; lean_object* v_res_3172_; 
v_sz_boxed_3170_ = lean_unbox_usize(v_sz_3167_);
lean_dec(v_sz_3167_);
v_i_boxed_3171_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3170_, v_i_boxed_3171_, v_bs_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3173_){
_start:
{
size_t v_sz_3174_; size_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_sz_3174_ = lean_array_size(v_a_3173_);
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3174_, v___x_3175_, v_a_3173_);
v___x_3177_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3178_){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_array_mk(v_a_3178_);
v___x_3180_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3181_){
_start:
{
if (lean_obj_tag(v_x_3181_) == 0)
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_box(0);
return v___x_3182_;
}
else
{
lean_object* v_val_3183_; lean_object* v___x_3184_; 
v_val_3183_ = lean_ctor_get(v_x_3181_, 0);
lean_inc(v_val_3183_);
lean_dec_ref_known(v_x_3181_, 1);
v___x_3184_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3183_);
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
if (lean_obj_tag(v_a_3185_) == 0)
{
lean_object* v___x_3187_; 
v___x_3187_ = l_List_reverse___redArg(v_a_3186_);
return v___x_3187_;
}
else
{
lean_object* v_head_3188_; lean_object* v_tail_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3199_; 
v_head_3188_ = lean_ctor_get(v_a_3185_, 0);
v_tail_3189_ = lean_ctor_get(v_a_3185_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_a_3185_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3191_ = v_a_3185_;
v_isShared_3192_ = v_isSharedCheck_3199_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_tail_3189_);
lean_inc(v_head_3188_);
lean_dec(v_a_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3199_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3193_ = l_Lean_JsonNumber_fromNat(v_head_3188_);
v___x_3194_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v_a_3186_);
lean_ctor_set(v___x_3191_, 0, v___x_3194_);
v___x_3196_ = v___x_3191_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_a_3186_);
v___x_3196_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
v_a_3185_ = v_tail_3189_;
v_a_3186_ = v___x_3196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3200_, size_t v_i_3201_, lean_object* v_bs_3202_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_lt(v_i_3201_, v_sz_3200_);
if (v___x_3203_ == 0)
{
return v_bs_3202_;
}
else
{
lean_object* v_v_3204_; lean_object* v_startPosLine_3205_; lean_object* v_startPosCharacter_3206_; lean_object* v_endPosLine_3207_; lean_object* v_endPosCharacter_3208_; lean_object* v___x_3209_; lean_object* v_bs_x27_3210_; lean_object* v___y_3212_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v_range_3222_; lean_object* v___x_3223_; 
v_v_3204_ = lean_array_uget(v_bs_3202_, v_i_3201_);
v_startPosLine_3205_ = lean_ctor_get(v_v_3204_, 0);
v_startPosCharacter_3206_ = lean_ctor_get(v_v_3204_, 1);
v_endPosLine_3207_ = lean_ctor_get(v_v_3204_, 2);
v_endPosCharacter_3208_ = lean_ctor_get(v_v_3204_, 3);
v___x_3209_ = lean_unsigned_to_nat(0u);
v_bs_x27_3210_ = lean_array_uset(v_bs_3202_, v_i_3201_, v___x_3209_);
v___x_3217_ = lean_box(0);
lean_inc(v_endPosCharacter_3208_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v_endPosCharacter_3208_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
lean_inc(v_endPosLine_3207_);
v___x_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_endPosLine_3207_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
lean_inc(v_startPosCharacter_3206_);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_startPosCharacter_3206_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
lean_inc(v_startPosLine_3205_);
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_startPosLine_3205_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v_range_3222_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3221_, v___x_3217_);
v___x_3223_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3204_);
lean_dec(v_v_3204_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = l_List_appendTR___redArg(v_range_3222_, v___x_3217_);
v___y_3212_ = v___x_3224_;
goto v___jp_3211_;
}
else
{
lean_object* v_val_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3234_; 
v_val_3225_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3227_ = v___x_3223_;
v_isShared_3228_ = v_isSharedCheck_3234_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_val_3225_);
lean_dec(v___x_3223_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3234_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 3);
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_val_3225_);
v___x_3230_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3217_);
v___x_3232_ = l_List_appendTR___redArg(v_range_3222_, v___x_3231_);
v___y_3212_ = v___x_3232_;
goto v___jp_3211_;
}
}
}
v___jp_3211_:
{
size_t v___x_3213_; size_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = ((size_t)1ULL);
v___x_3214_ = lean_usize_add(v_i_3201_, v___x_3213_);
v___x_3215_ = lean_array_uset(v_bs_x27_3210_, v_i_3201_, v___y_3212_);
v_i_3201_ = v___x_3214_;
v_bs_3202_ = v___x_3215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3235_, lean_object* v_i_3236_, lean_object* v_bs_3237_){
_start:
{
size_t v_sz_boxed_3238_; size_t v_i_boxed_3239_; lean_object* v_res_3240_; 
v_sz_boxed_3238_ = lean_unbox_usize(v_sz_3235_);
lean_dec(v_sz_3235_);
v_i_boxed_3239_ = lean_unbox_usize(v_i_3236_);
lean_dec(v_i_3236_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3238_, v_i_boxed_3239_, v_bs_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_bs_3243_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3244_ == 0)
{
return v_bs_3243_;
}
else
{
lean_object* v_v_3245_; lean_object* v___x_3246_; lean_object* v_bs_x27_3247_; lean_object* v___x_3248_; size_t v___x_3249_; size_t v___x_3250_; lean_object* v___x_3251_; 
v_v_3245_ = lean_array_uget(v_bs_3243_, v_i_3242_);
v___x_3246_ = lean_unsigned_to_nat(0u);
v_bs_x27_3247_ = lean_array_uset(v_bs_3243_, v_i_3242_, v___x_3246_);
v___x_3248_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3245_);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3242_, v___x_3249_);
v___x_3251_ = lean_array_uset(v_bs_x27_3247_, v_i_3242_, v___x_3248_);
v_i_3242_ = v___x_3250_;
v_bs_3243_ = v___x_3251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3253_, lean_object* v_i_3254_, lean_object* v_bs_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3253_);
lean_dec(v_sz_3253_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3256_, v_i_boxed_3257_, v_bs_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3259_){
_start:
{
size_t v_sz_3260_; size_t v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_sz_3260_ = lean_array_size(v_a_3259_);
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3260_, v___x_3261_, v_a_3259_);
v___x_3263_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
if (lean_obj_tag(v_a_3264_) == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = l_List_reverse___redArg(v_a_3265_);
return v___x_3266_;
}
else
{
lean_object* v_head_3267_; lean_object* v_snd_3268_; lean_object* v_tail_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3338_; 
v_head_3267_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_head_3267_);
v_snd_3268_ = lean_ctor_get(v_head_3267_, 1);
lean_inc(v_snd_3268_);
v_tail_3269_ = lean_ctor_get(v_a_3264_, 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_a_3264_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_a_3264_, 0);
lean_dec(v_unused_3339_);
v___x_3271_ = v_a_3264_;
v_isShared_3272_ = v_isSharedCheck_3338_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_tail_3269_);
lean_dec(v_a_3264_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3338_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v_fst_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3336_; 
v_fst_3273_ = lean_ctor_get(v_head_3267_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_head_3267_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_head_3267_, 1);
lean_dec(v_unused_3337_);
v___x_3275_ = v_head_3267_;
v_isShared_3276_ = v_isSharedCheck_3336_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_fst_3273_);
lean_dec(v_head_3267_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3336_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_definition_x3f_3277_; lean_object* v_usages_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3335_; 
v_definition_x3f_3277_ = lean_ctor_get(v_snd_3268_, 0);
v_usages_3278_ = lean_ctor_get(v_snd_3268_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_snd_3268_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3280_ = v_snd_3268_;
v_isShared_3281_ = v_isSharedCheck_3335_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_usages_3278_);
lean_inc(v_definition_x3f_3277_);
lean_dec(v_snd_3268_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3335_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___y_3286_; lean_object* v___y_3309_; 
v___x_3282_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3273_);
v___x_3283_ = l_Lean_Json_compress(v___x_3282_);
v___x_3284_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3277_) == 0)
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_box(0);
v___y_3286_ = v___x_3311_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3312_; lean_object* v_startPosLine_3313_; lean_object* v_startPosCharacter_3314_; lean_object* v_endPosLine_3315_; lean_object* v_endPosCharacter_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v_range_3322_; lean_object* v___x_3323_; 
v_val_3312_ = lean_ctor_get(v_definition_x3f_3277_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v_definition_x3f_3277_, 1);
v_startPosLine_3313_ = lean_ctor_get(v_val_3312_, 0);
v_startPosCharacter_3314_ = lean_ctor_get(v_val_3312_, 1);
v_endPosLine_3315_ = lean_ctor_get(v_val_3312_, 2);
v_endPosCharacter_3316_ = lean_ctor_get(v_val_3312_, 3);
v___x_3317_ = lean_box(0);
lean_inc(v_endPosCharacter_3316_);
v___x_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3318_, 0, v_endPosCharacter_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
lean_inc(v_endPosLine_3315_);
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v_endPosLine_3315_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
lean_inc(v_startPosCharacter_3314_);
v___x_3320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3320_, 0, v_startPosCharacter_3314_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
lean_inc(v_startPosLine_3313_);
v___x_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_startPosLine_3313_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v_range_3322_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3321_, v___x_3317_);
v___x_3323_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3312_);
lean_dec(v_val_3312_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = l_List_appendTR___redArg(v_range_3322_, v___x_3317_);
v___y_3309_ = v___x_3324_;
goto v___jp_3308_;
}
else
{
lean_object* v_val_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3334_; 
v_val_3325_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3327_ = v___x_3323_;
v_isShared_3328_ = v_isSharedCheck_3334_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_val_3325_);
lean_dec(v___x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3334_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 3);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_val_3325_);
v___x_3330_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3317_);
v___x_3332_ = l_List_appendTR___redArg(v_range_3322_, v___x_3331_);
v___y_3309_ = v___x_3332_;
goto v___jp_3308_;
}
}
}
}
v___jp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3286_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v___x_3287_);
lean_ctor_set(v___x_3275_, 0, v___x_3284_);
v___x_3289_ = v___x_3275_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; size_t v_sz_3291_; size_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3290_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3291_ = lean_array_size(v_usages_3278_);
v___x_3292_ = ((size_t)0ULL);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3291_, v___x_3292_, v_usages_3278_);
v___x_3294_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3293_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3294_);
lean_ctor_set(v___x_3280_, 0, v___x_3290_);
v___x_3296_ = v___x_3280_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 1, v___x_3297_);
lean_ctor_set(v___x_3271_, 0, v___x_3296_);
v___x_3299_ = v___x_3271_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3289_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Json_mkObj(v___x_3300_);
lean_dec_ref_known(v___x_3300_, 2);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3283_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_a_3265_);
v_a_3264_ = v_tail_3269_;
v_a_3265_ = v___x_3303_;
goto _start;
}
}
}
}
v___jp_3308_:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___y_3309_);
v___y_3286_ = v___x_3310_;
goto v___jp_3285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
if (lean_obj_tag(v_a_3340_) == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = l_List_reverse___redArg(v_a_3341_);
return v___x_3342_;
}
else
{
lean_object* v_head_3343_; lean_object* v_snd_3344_; lean_object* v_tail_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3397_; 
v_head_3343_ = lean_ctor_get(v_a_3340_, 0);
lean_inc(v_head_3343_);
v_snd_3344_ = lean_ctor_get(v_head_3343_, 1);
lean_inc(v_snd_3344_);
v_tail_3345_ = lean_ctor_get(v_a_3340_, 1);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_a_3340_, 0);
lean_dec(v_unused_3398_);
v___x_3347_ = v_a_3340_;
v_isShared_3348_ = v_isSharedCheck_3397_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_tail_3345_);
lean_dec(v_a_3340_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3397_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_fst_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3395_; 
v_fst_3349_ = lean_ctor_get(v_head_3343_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_head_3343_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; 
v_unused_3396_ = lean_ctor_get(v_head_3343_, 1);
lean_dec(v_unused_3396_);
v___x_3351_ = v_head_3343_;
v_isShared_3352_ = v_isSharedCheck_3395_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_fst_3349_);
lean_dec(v_head_3343_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3395_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_rangeStartPosLine_3353_; lean_object* v_rangeStartPosCharacter_3354_; lean_object* v_rangeEndPosLine_3355_; lean_object* v_rangeEndPosCharacter_3356_; lean_object* v_selectionRangeStartPosLine_3357_; lean_object* v_selectionRangeStartPosCharacter_3358_; lean_object* v_selectionRangeEndPosLine_3359_; lean_object* v_selectionRangeEndPosCharacter_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v_rangeStartPosLine_3353_ = lean_ctor_get(v_snd_3344_, 0);
lean_inc(v_rangeStartPosLine_3353_);
v_rangeStartPosCharacter_3354_ = lean_ctor_get(v_snd_3344_, 1);
lean_inc(v_rangeStartPosCharacter_3354_);
v_rangeEndPosLine_3355_ = lean_ctor_get(v_snd_3344_, 2);
lean_inc(v_rangeEndPosLine_3355_);
v_rangeEndPosCharacter_3356_ = lean_ctor_get(v_snd_3344_, 3);
lean_inc(v_rangeEndPosCharacter_3356_);
v_selectionRangeStartPosLine_3357_ = lean_ctor_get(v_snd_3344_, 4);
lean_inc(v_selectionRangeStartPosLine_3357_);
v_selectionRangeStartPosCharacter_3358_ = lean_ctor_get(v_snd_3344_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3358_);
v_selectionRangeEndPosLine_3359_ = lean_ctor_get(v_snd_3344_, 6);
lean_inc(v_selectionRangeEndPosLine_3359_);
v_selectionRangeEndPosCharacter_3360_ = lean_ctor_get(v_snd_3344_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3360_);
lean_dec(v_snd_3344_);
v___x_3361_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3353_);
v___x_3362_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3354_);
v___x_3364_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
v___x_3365_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3355_);
v___x_3366_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3356_);
v___x_3368_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3357_);
v___x_3370_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3358_);
v___x_3372_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
v___x_3373_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3359_);
v___x_3374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3360_);
v___x_3376_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
v___x_3377_ = lean_unsigned_to_nat(8u);
v___x_3378_ = lean_mk_empty_array_with_capacity(v___x_3377_);
v___x_3379_ = lean_array_push(v___x_3378_, v___x_3362_);
v___x_3380_ = lean_array_push(v___x_3379_, v___x_3364_);
v___x_3381_ = lean_array_push(v___x_3380_, v___x_3366_);
v___x_3382_ = lean_array_push(v___x_3381_, v___x_3368_);
v___x_3383_ = lean_array_push(v___x_3382_, v___x_3370_);
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3372_);
v___x_3385_ = lean_array_push(v___x_3384_, v___x_3374_);
v___x_3386_ = lean_array_push(v___x_3385_, v___x_3376_);
v___x_3387_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v___x_3387_);
v___x_3389_ = v___x_3351_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_fst_3349_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3341_);
lean_ctor_set(v___x_3347_, 0, v___x_3389_);
v___x_3391_ = v___x_3347_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_a_3341_);
v___x_3391_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_a_3340_ = v_tail_3345_;
v_a_3341_ = v___x_3391_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3399_, lean_object* v_x_3400_){
_start:
{
if (lean_obj_tag(v_x_3400_) == 0)
{
lean_object* v_k_3401_; lean_object* v_v_3402_; lean_object* v_l_3403_; lean_object* v_r_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_k_3401_ = lean_ctor_get(v_x_3400_, 1);
v_v_3402_ = lean_ctor_get(v_x_3400_, 2);
v_l_3403_ = lean_ctor_get(v_x_3400_, 3);
v_r_3404_ = lean_ctor_get(v_x_3400_, 4);
v___x_3405_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3399_, v_r_3404_);
lean_inc(v_v_3402_);
lean_inc(v_k_3401_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_k_3401_);
lean_ctor_set(v___x_3406_, 1, v_v_3402_);
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
v_init_3399_ = v___x_3407_;
v_x_3400_ = v_l_3403_;
goto _start;
}
else
{
return v_init_3399_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3409_, lean_object* v_x_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3409_, v_x_3410_);
lean_dec(v_x_3410_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3412_){
_start:
{
lean_object* v_version_3413_; lean_object* v_references_3414_; lean_object* v_decls_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_version_3413_ = lean_ctor_get(v_x_3412_, 0);
lean_inc(v_version_3413_);
v_references_3414_ = lean_ctor_get(v_x_3412_, 1);
lean_inc(v_references_3414_);
v_decls_3415_ = lean_ctor_get(v_x_3412_, 2);
lean_inc(v_decls_3415_);
lean_dec_ref(v_x_3412_);
v___x_3416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3417_ = l_Lean_JsonNumber_fromNat(v_version_3413_);
v___x_3418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3416_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3423_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3420_, v_references_3414_);
lean_dec(v_references_3414_);
v___x_3424_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3423_, v___x_3420_);
v___x_3425_ = l_Lean_Json_mkObj(v___x_3424_);
lean_dec(v___x_3424_);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3422_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3420_);
v___x_3428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3429_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3420_, v_decls_3415_);
lean_dec(v_decls_3415_);
v___x_3430_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3429_, v___x_3420_);
v___x_3431_ = l_Lean_Json_mkObj(v___x_3430_);
lean_dec(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3428_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v___x_3420_);
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3420_);
v___x_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3427_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3421_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3438_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3436_, v___x_3437_);
v___x_3439_ = l_Lean_Json_mkObj(v___x_3438_);
lean_dec(v___x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_bs_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v_bs_3444_);
return v___x_3446_;
}
else
{
lean_object* v_v_3447_; lean_object* v___x_3448_; 
v_v_3447_ = lean_array_uget_borrowed(v_bs_3444_, v_i_3443_);
lean_inc(v_v_3447_);
v___x_3448_ = l_Lean_Json_getStr_x3f(v_v_3447_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_bs_3444_);
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v_bs_x27_3459_; size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v_a_3457_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3458_ = lean_unsigned_to_nat(0u);
v_bs_x27_3459_ = lean_array_uset(v_bs_3444_, v_i_3443_, v___x_3458_);
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3443_, v___x_3460_);
v___x_3462_ = lean_array_uset(v_bs_x27_3459_, v_i_3443_, v_a_3457_);
v_i_3443_ = v___x_3461_;
v_bs_3444_ = v___x_3462_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_bs_3466_){
_start:
{
size_t v_sz_boxed_3467_; size_t v_i_boxed_3468_; lean_object* v_res_3469_; 
v_sz_boxed_3467_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3467_, v_i_boxed_3468_, v_bs_3466_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3470_){
_start:
{
if (lean_obj_tag(v_x_3470_) == 4)
{
lean_object* v_elems_3471_; size_t v_sz_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
v_elems_3471_ = lean_ctor_get(v_x_3470_, 0);
lean_inc_ref(v_elems_3471_);
lean_dec_ref_known(v_x_3470_, 1);
v_sz_3472_ = lean_array_size(v_elems_3471_);
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3472_, v___x_3473_, v_elems_3471_);
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3475_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3476_ = lean_unsigned_to_nat(80u);
v___x_3477_ = l_Lean_Json_pretty(v_x_3470_, v___x_3476_);
v___x_3478_ = lean_string_append(v___x_3475_, v___x_3477_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3480_ = lean_string_append(v___x_3478_, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3482_, lean_object* v_k_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = l_Lean_Json_getObjValD(v_j_3482_, v_k_3483_);
v___x_3485_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3486_, lean_object* v_k_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3486_, v_k_3487_);
lean_dec_ref(v_k_3487_);
return v_res_3488_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = 1;
v___x_3496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3496_, v___x_3495_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3499_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3500_ = lean_string_append(v___x_3499_, v___x_3498_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = 1;
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3505_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3504_, v___x_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3508_ = lean_string_append(v___x_3507_, v___x_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3511_ = lean_string_append(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3512_){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3514_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3512_, v___x_3513_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3524_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3524_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3524_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3519_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3520_ = lean_string_append(v___x_3519_, v_a_3515_);
lean_dec(v_a_3515_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3520_);
v___x_3522_ = v___x_3517_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3514_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3514_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3535_, size_t v_i_3536_, lean_object* v_bs_3537_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_lt(v_i_3536_, v_sz_3535_);
if (v___x_3538_ == 0)
{
return v_bs_3537_;
}
else
{
lean_object* v_v_3539_; lean_object* v___x_3540_; lean_object* v_bs_x27_3541_; lean_object* v___x_3542_; size_t v___x_3543_; size_t v___x_3544_; lean_object* v___x_3545_; 
v_v_3539_ = lean_array_uget(v_bs_3537_, v_i_3536_);
v___x_3540_ = lean_unsigned_to_nat(0u);
v_bs_x27_3541_ = lean_array_uset(v_bs_3537_, v_i_3536_, v___x_3540_);
v___x_3542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3542_, 0, v_v_3539_);
v___x_3543_ = ((size_t)1ULL);
v___x_3544_ = lean_usize_add(v_i_3536_, v___x_3543_);
v___x_3545_ = lean_array_uset(v_bs_x27_3541_, v_i_3536_, v___x_3542_);
v_i_3536_ = v___x_3544_;
v_bs_3537_ = v___x_3545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3547_, lean_object* v_i_3548_, lean_object* v_bs_3549_){
_start:
{
size_t v_sz_boxed_3550_; size_t v_i_boxed_3551_; lean_object* v_res_3552_; 
v_sz_boxed_3550_ = lean_unbox_usize(v_sz_3547_);
lean_dec(v_sz_3547_);
v_i_boxed_3551_ = lean_unbox_usize(v_i_3548_);
lean_dec(v_i_3548_);
v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3550_, v_i_boxed_3551_, v_bs_3549_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3553_){
_start:
{
size_t v_sz_3554_; size_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_sz_3554_ = lean_array_size(v_a_3553_);
v___x_3555_ = ((size_t)0ULL);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3554_, v___x_3555_, v_a_3553_);
v___x_3557_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3558_){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3559_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3560_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3558_);
v___x_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3562_);
v___x_3565_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3566_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3564_, v___x_3565_);
v___x_3567_ = l_Lean_Json_mkObj(v___x_3566_);
lean_dec(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3570_, lean_object* v_k_3571_){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = l_Lean_Json_getObjValD(v_j_3570_, v_k_3571_);
v___x_3573_ = l_Lean_Json_getStr_x3f(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3574_, lean_object* v_k_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3574_, v_k_3575_);
lean_dec_ref(v_k_3575_);
return v_res_3576_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = 1;
v___x_3584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3585_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3584_, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3587_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3588_ = lean_string_append(v___x_3587_, v___x_3586_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = 1;
v___x_3592_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3592_, v___x_3591_);
return v___x_3593_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3595_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3596_ = lean_string_append(v___x_3595_, v___x_3594_);
return v___x_3596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3598_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3599_ = lean_string_append(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3602_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3600_, v___x_3601_);
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
v___x_3607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
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
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3624_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3625_, 0, v_x_3623_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_box(0);
v___x_3628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v___x_3627_);
v___x_3630_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3631_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3629_, v___x_3630_);
v___x_3632_ = l_Lean_Json_mkObj(v___x_3631_);
lean_dec(v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl(lean_object* v_x_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_obj_tag_nat(v_x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl___boxed(lean_object* v_x_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Lsp_OpenNamespace_ctorIdx___impl(v_x_3637_);
lean_dec_ref(v_x_3637_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3639_, lean_object* v_k_3640_){
_start:
{
if (lean_obj_tag(v_t_3639_) == 0)
{
lean_object* v_namespace_3641_; lean_object* v_exceptions_3642_; lean_object* v___x_3643_; 
v_namespace_3641_ = lean_ctor_get(v_t_3639_, 0);
lean_inc(v_namespace_3641_);
v_exceptions_3642_ = lean_ctor_get(v_t_3639_, 1);
lean_inc_ref(v_exceptions_3642_);
lean_dec_ref_known(v_t_3639_, 2);
v___x_3643_ = lean_apply_2(v_k_3640_, v_namespace_3641_, v_exceptions_3642_);
return v___x_3643_;
}
else
{
lean_object* v_from_3644_; lean_object* v_to_3645_; lean_object* v___x_3646_; 
v_from_3644_ = lean_ctor_get(v_t_3639_, 0);
lean_inc(v_from_3644_);
v_to_3645_ = lean_ctor_get(v_t_3639_, 1);
lean_inc(v_to_3645_);
lean_dec_ref_known(v_t_3639_, 2);
v___x_3646_ = lean_apply_2(v_k_3640_, v_from_3644_, v_to_3645_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3647_, lean_object* v_ctorIdx_3648_, lean_object* v_t_3649_, lean_object* v_h_3650_, lean_object* v_k_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3649_, v_k_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3653_, lean_object* v_ctorIdx_3654_, lean_object* v_t_3655_, lean_object* v_h_3656_, lean_object* v_k_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3653_, v_ctorIdx_3654_, v_t_3655_, v_h_3656_, v_k_3657_);
lean_dec(v_ctorIdx_3654_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3659_, lean_object* v_allExcept_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3659_, v_allExcept_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3662_, lean_object* v_t_3663_, lean_object* v_h_3664_, lean_object* v_allExcept_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3663_, v_allExcept_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3667_, lean_object* v_renamed_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3667_, v_renamed_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3670_, lean_object* v_t_3671_, lean_object* v_h_3672_, lean_object* v_renamed_3673_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3671_, v_renamed_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3675_, size_t v_i_3676_, lean_object* v_bs_3677_){
_start:
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_usize_dec_lt(v_i_3676_, v_sz_3675_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_bs_3677_);
return v___x_3679_;
}
else
{
lean_object* v_v_3680_; lean_object* v___x_3681_; 
v_v_3680_ = lean_array_uget_borrowed(v_bs_3677_, v_i_3676_);
lean_inc(v_v_3680_);
v___x_3681_ = l_Lean_Name_fromJson_x3f(v_v_3680_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v_bs_3677_);
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
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
lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v_bs_x27_3692_; size_t v___x_3693_; size_t v___x_3694_; lean_object* v___x_3695_; 
v_a_3690_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3681_, 1);
v___x_3691_ = lean_unsigned_to_nat(0u);
v_bs_x27_3692_ = lean_array_uset(v_bs_3677_, v_i_3676_, v___x_3691_);
v___x_3693_ = ((size_t)1ULL);
v___x_3694_ = lean_usize_add(v_i_3676_, v___x_3693_);
v___x_3695_ = lean_array_uset(v_bs_x27_3692_, v_i_3676_, v_a_3690_);
v_i_3676_ = v___x_3694_;
v_bs_3677_ = v___x_3695_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3697_, lean_object* v_i_3698_, lean_object* v_bs_3699_){
_start:
{
size_t v_sz_boxed_3700_; size_t v_i_boxed_3701_; lean_object* v_res_3702_; 
v_sz_boxed_3700_ = lean_unbox_usize(v_sz_3697_);
lean_dec(v_sz_3697_);
v_i_boxed_3701_ = lean_unbox_usize(v_i_3698_);
lean_dec(v_i_3698_);
v_res_3702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3700_, v_i_boxed_3701_, v_bs_3699_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 4)
{
lean_object* v_elems_3704_; size_t v_sz_3705_; size_t v___x_3706_; lean_object* v___x_3707_; 
v_elems_3704_ = lean_ctor_get(v_x_3703_, 0);
lean_inc_ref(v_elems_3704_);
lean_dec_ref_known(v_x_3703_, 1);
v_sz_3705_ = lean_array_size(v_elems_3704_);
v___x_3706_ = ((size_t)0ULL);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3705_, v___x_3706_, v_elems_3704_);
return v___x_3707_;
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3708_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3709_ = lean_unsigned_to_nat(80u);
v___x_3710_ = l_Lean_Json_pretty(v_x_3703_, v___x_3709_);
v___x_3711_ = lean_string_append(v___x_3708_, v___x_3710_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3713_ = lean_string_append(v___x_3711_, v___x_3712_);
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
return v___x_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3749_){
_start:
{
lean_object* v___x_3750_; 
lean_inc(v_json_3749_);
v___x_3750_ = l_Lean_Json_getTag_x3f(v_json_3749_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3751_; 
lean_dec(v_json_3749_);
v___x_3751_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3751_;
}
else
{
lean_object* v_val_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v_val_3752_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_val_3752_);
lean_dec_ref_known(v___x_3750_, 1);
v___x_3753_ = lean_box(0);
v___x_3754_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3755_ = lean_string_dec_eq(v_val_3752_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3757_ = lean_string_dec_eq(v_val_3752_, v___x_3756_);
lean_dec(v_val_3752_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; 
lean_dec(v_json_3749_);
v___x_3758_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3758_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = lean_unsigned_to_nat(2u);
v___x_3760_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3761_ = l_Lean_Json_parseCtorFields(v_json_3749_, v___x_3756_, v___x_3759_, v___x_3760_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_a_3770_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3771_ = lean_unsigned_to_nat(0u);
v___x_3772_ = lean_array_get_borrowed(v___x_3753_, v_a_3770_, v___x_3771_);
lean_inc(v___x_3772_);
v___x_3773_ = l_Lean_Name_fromJson_x3f(v___x_3772_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec(v_a_3770_);
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3782_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3783_ = lean_unsigned_to_nat(1u);
v___x_3784_ = lean_array_get(v___x_3753_, v_a_3770_, v___x_3783_);
lean_dec(v_a_3770_);
v___x_3785_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3784_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v_a_3782_);
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3802_; 
v_a_3794_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3796_ = v___x_3785_;
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3785_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3782_);
lean_ctor_set(v___x_3798_, 1, v_a_3794_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec(v_val_3752_);
v___x_3803_ = lean_unsigned_to_nat(2u);
v___x_3804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3805_ = l_Lean_Json_parseCtorFields(v_json_3749_, v___x_3754_, v___x_3803_, v___x_3804_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_a_3814_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3805_, 1);
v___x_3815_ = lean_unsigned_to_nat(0u);
v___x_3816_ = lean_array_get_borrowed(v___x_3753_, v_a_3814_, v___x_3815_);
lean_inc(v___x_3816_);
v___x_3817_ = l_Lean_Name_fromJson_x3f(v___x_3816_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_a_3814_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_a_3826_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3827_ = lean_unsigned_to_nat(1u);
v___x_3828_ = lean_array_get(v___x_3753_, v_a_3814_, v___x_3827_);
lean_dec(v_a_3814_);
v___x_3829_ = l_Lean_Name_fromJson_x3f(v___x_3828_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_a_3826_);
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3846_; 
v_a_3838_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3840_ = v___x_3829_;
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3829_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_a_3826_);
lean_ctor_set(v___x_3842_, 1, v_a_3838_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3842_);
v___x_3844_ = v___x_3840_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3849_, size_t v_i_3850_, lean_object* v_bs_3851_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_usize_dec_lt(v_i_3850_, v_sz_3849_);
if (v___x_3852_ == 0)
{
return v_bs_3851_;
}
else
{
lean_object* v_v_3853_; lean_object* v___x_3854_; lean_object* v_bs_x27_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; size_t v___x_3858_; size_t v___x_3859_; lean_object* v___x_3860_; 
v_v_3853_ = lean_array_uget(v_bs_3851_, v_i_3850_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v_bs_x27_3855_ = lean_array_uset(v_bs_3851_, v_i_3850_, v___x_3854_);
v___x_3856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3853_, v___x_3852_);
v___x_3857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3850_, v___x_3858_);
v___x_3860_ = lean_array_uset(v_bs_x27_3855_, v_i_3850_, v___x_3857_);
v_i_3850_ = v___x_3859_;
v_bs_3851_ = v___x_3860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_bs_3864_){
_start:
{
size_t v_sz_boxed_3865_; size_t v_i_boxed_3866_; lean_object* v_res_3867_; 
v_sz_boxed_3865_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3866_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3865_, v_i_boxed_3866_, v_bs_3864_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3868_){
_start:
{
size_t v_sz_3869_; size_t v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v_sz_3869_ = lean_array_size(v_a_3868_);
v___x_3870_ = ((size_t)0ULL);
v___x_3871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3869_, v___x_3870_, v_a_3868_);
v___x_3872_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3873_){
_start:
{
if (lean_obj_tag(v_x_3873_) == 0)
{
lean_object* v_namespace_3874_; lean_object* v_exceptions_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3897_; 
v_namespace_3874_ = lean_ctor_get(v_x_3873_, 0);
v_exceptions_3875_ = lean_ctor_get(v_x_3873_, 1);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_x_3873_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3877_ = v_x_3873_;
v_isShared_3878_ = v_isSharedCheck_3897_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_exceptions_3875_);
lean_inc(v_namespace_3874_);
lean_dec(v_x_3873_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3897_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3879_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3880_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3881_ = 1;
v___x_3882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3874_, v___x_3881_);
v___x_3883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 1, v___x_3883_);
lean_ctor_set(v___x_3877_, 0, v___x_3880_);
v___x_3885_ = v___x_3877_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3886_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3887_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3875_);
v___x_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_box(0);
v___x_3890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3885_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_Lean_Json_mkObj(v___x_3891_);
lean_dec_ref_known(v___x_3891_, 2);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3879_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___x_3889_);
v___x_3895_ = l_Lean_Json_mkObj(v___x_3894_);
lean_dec_ref_known(v___x_3894_, 2);
return v___x_3895_;
}
}
}
else
{
lean_object* v_from_3898_; lean_object* v_to_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3922_; 
v_from_3898_ = lean_ctor_get(v_x_3873_, 0);
v_to_3899_ = lean_ctor_get(v_x_3873_, 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_x_3873_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3901_ = v_x_3873_;
v_isShared_3902_ = v_isSharedCheck_3922_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_to_3899_);
lean_inc(v_from_3898_);
lean_dec(v_x_3873_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3922_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3903_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3904_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3905_ = 1;
v___x_3906_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3898_, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 0);
lean_ctor_set(v___x_3901_, 1, v___x_3907_);
lean_ctor_set(v___x_3901_, 0, v___x_3904_);
v___x_3909_ = v___x_3901_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3910_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3911_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3899_, v___x_3905_);
v___x_3912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3910_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_box(0);
v___x_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3909_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = l_Lean_Json_mkObj(v___x_3916_);
lean_dec_ref_known(v___x_3916_, 2);
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3903_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
lean_ctor_set(v___x_3919_, 1, v___x_3914_);
v___x_3920_ = l_Lean_Json_mkObj(v___x_3919_);
lean_dec_ref_known(v___x_3919_, 2);
return v___x_3920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3925_, size_t v_i_3926_, lean_object* v_bs_3927_){
_start:
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_usize_dec_lt(v_i_3926_, v_sz_3925_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_bs_3927_);
return v___x_3929_;
}
else
{
lean_object* v_v_3930_; lean_object* v___x_3931_; 
v_v_3930_ = lean_array_uget_borrowed(v_bs_3927_, v_i_3926_);
lean_inc(v_v_3930_);
v___x_3931_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_bs_3927_);
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3931_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3931_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3941_; lean_object* v_bs_x27_3942_; size_t v___x_3943_; size_t v___x_3944_; lean_object* v___x_3945_; 
v_a_3940_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3941_ = lean_unsigned_to_nat(0u);
v_bs_x27_3942_ = lean_array_uset(v_bs_3927_, v_i_3926_, v___x_3941_);
v___x_3943_ = ((size_t)1ULL);
v___x_3944_ = lean_usize_add(v_i_3926_, v___x_3943_);
v___x_3945_ = lean_array_uset(v_bs_x27_3942_, v_i_3926_, v_a_3940_);
v_i_3926_ = v___x_3944_;
v_bs_3927_ = v___x_3945_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3947_, lean_object* v_i_3948_, lean_object* v_bs_3949_){
_start:
{
size_t v_sz_boxed_3950_; size_t v_i_boxed_3951_; lean_object* v_res_3952_; 
v_sz_boxed_3950_ = lean_unbox_usize(v_sz_3947_);
lean_dec(v_sz_3947_);
v_i_boxed_3951_ = lean_unbox_usize(v_i_3948_);
lean_dec(v_i_3948_);
v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3950_, v_i_boxed_3951_, v_bs_3949_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_3953_){
_start:
{
if (lean_obj_tag(v_x_3953_) == 4)
{
lean_object* v_elems_3954_; size_t v_sz_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v_elems_3954_ = lean_ctor_get(v_x_3953_, 0);
lean_inc_ref(v_elems_3954_);
lean_dec_ref_known(v_x_3953_, 1);
v_sz_3955_ = lean_array_size(v_elems_3954_);
v___x_3956_ = ((size_t)0ULL);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_3955_, v___x_3956_, v_elems_3954_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3958_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3959_ = lean_unsigned_to_nat(80u);
v___x_3960_ = l_Lean_Json_pretty(v_x_3953_, v___x_3959_);
v___x_3961_ = lean_string_append(v___x_3958_, v___x_3960_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3963_ = lean_string_append(v___x_3961_, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_3965_, lean_object* v_k_3966_){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = l_Lean_Json_getObjValD(v_j_3965_, v_k_3966_);
v___x_3968_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_3969_, lean_object* v_k_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_3969_, v_k_3970_);
lean_dec_ref(v_k_3970_);
return v_res_3971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = 1;
v___x_3979_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_3980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3979_, v___x_3978_);
return v___x_3980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_3983_ = lean_string_append(v___x_3982_, v___x_3981_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = 1;
v___x_3987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_3988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3987_, v___x_3986_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_3990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_3991_ = lean_string_append(v___x_3990_, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_3994_ = lean_string_append(v___x_3993_, v___x_3992_);
return v___x_3994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = 1;
v___x_3999_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4000_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3999_, v___x_3998_);
return v___x_4000_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4003_ = lean_string_append(v___x_4002_, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4006_ = lean_string_append(v___x_4005_, v___x_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4007_){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4007_);
v___x_4009_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4007_, v___x_4008_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v_json_4007_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4019_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4019_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4014_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4015_ = lean_string_append(v___x_4014_, v_a_4010_);
lean_dec(v_a_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4015_);
v___x_4017_ = v___x_4012_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v_a_4020_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4021_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4022_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4007_, v___x_4021_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_a_4020_);
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4032_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4027_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4028_ = lean_string_append(v___x_4027_, v_a_4023_);
lean_dec(v_a_4023_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4041_; 
v_a_4033_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4035_ = v___x_4022_;
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4022_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4041_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v_a_4020_);
lean_ctor_set(v___x_4037_, 1, v_a_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4037_);
v___x_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4044_, size_t v_i_4045_, lean_object* v_bs_4046_){
_start:
{
uint8_t v___x_4047_; 
v___x_4047_ = lean_usize_dec_lt(v_i_4045_, v_sz_4044_);
if (v___x_4047_ == 0)
{
return v_bs_4046_;
}
else
{
lean_object* v_v_4048_; lean_object* v___x_4049_; lean_object* v_bs_x27_4050_; lean_object* v___x_4051_; size_t v___x_4052_; size_t v___x_4053_; lean_object* v___x_4054_; 
v_v_4048_ = lean_array_uget(v_bs_4046_, v_i_4045_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v_bs_x27_4050_ = lean_array_uset(v_bs_4046_, v_i_4045_, v___x_4049_);
v___x_4051_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4048_);
v___x_4052_ = ((size_t)1ULL);
v___x_4053_ = lean_usize_add(v_i_4045_, v___x_4052_);
v___x_4054_ = lean_array_uset(v_bs_x27_4050_, v_i_4045_, v___x_4051_);
v_i_4045_ = v___x_4053_;
v_bs_4046_ = v___x_4054_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4056_, lean_object* v_i_4057_, lean_object* v_bs_4058_){
_start:
{
size_t v_sz_boxed_4059_; size_t v_i_boxed_4060_; lean_object* v_res_4061_; 
v_sz_boxed_4059_ = lean_unbox_usize(v_sz_4056_);
lean_dec(v_sz_4056_);
v_i_boxed_4060_ = lean_unbox_usize(v_i_4057_);
lean_dec(v_i_4057_);
v_res_4061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4059_, v_i_boxed_4060_, v_bs_4058_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4062_){
_start:
{
size_t v_sz_4063_; size_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_sz_4063_ = lean_array_size(v_a_4062_);
v___x_4064_ = ((size_t)0ULL);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4063_, v___x_4064_, v_a_4062_);
v___x_4066_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4067_){
_start:
{
lean_object* v_identifier_4068_; lean_object* v_openNamespaces_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4089_; 
v_identifier_4068_ = lean_ctor_get(v_x_4067_, 0);
v_openNamespaces_4069_ = lean_ctor_get(v_x_4067_, 1);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_x_4067_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4071_ = v_x_4067_;
v_isShared_4072_ = v_isSharedCheck_4089_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_openNamespaces_4069_);
lean_inc(v_identifier_4068_);
lean_dec(v_x_4067_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4089_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4073_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4074_, 0, v_identifier_4068_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 1, v___x_4074_);
lean_ctor_set(v___x_4071_, 0, v___x_4073_);
v___x_4076_ = v___x_4071_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4080_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4069_);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v___x_4077_);
v___x_4083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
lean_ctor_set(v___x_4083_, 1, v___x_4077_);
v___x_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4078_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4086_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4084_, v___x_4085_);
v___x_4087_ = l_Lean_Json_mkObj(v___x_4086_);
lean_dec(v___x_4086_);
return v___x_4087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4095_, lean_object* v_k_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Json_getObjValD(v_j_4095_, v_k_4096_);
switch(lean_obj_tag(v___x_4097_))
{
case 3:
{
lean_object* v_s_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4106_; 
v_s_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4106_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_s_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4106_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set_tag(v___x_4100_, 0);
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_s_4098_);
v___x_4103_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
}
case 2:
{
lean_object* v_n_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4115_; 
v_n_4107_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4109_ = v___x_4097_;
v_isShared_4110_ = v_isSharedCheck_4115_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_n_4107_);
lean_dec(v___x_4097_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4115_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 1);
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_n_4107_);
v___x_4112_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
}
default: 
{
lean_object* v___x_4116_; 
lean_dec(v___x_4097_);
v___x_4116_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4117_, lean_object* v_k_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4117_, v_k_4118_);
lean_dec_ref(v_k_4118_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4120_, size_t v_i_4121_, lean_object* v_bs_4122_){
_start:
{
uint8_t v___x_4123_; 
v___x_4123_ = lean_usize_dec_lt(v_i_4121_, v_sz_4120_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_bs_4122_);
return v___x_4124_;
}
else
{
lean_object* v_v_4125_; lean_object* v___x_4126_; 
v_v_4125_ = lean_array_uget_borrowed(v_bs_4122_, v_i_4121_);
lean_inc(v_v_4125_);
v___x_4126_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4125_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v_bs_4122_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v_bs_x27_4137_; size_t v___x_4138_; size_t v___x_4139_; lean_object* v___x_4140_; 
v_a_4135_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4136_ = lean_unsigned_to_nat(0u);
v_bs_x27_4137_ = lean_array_uset(v_bs_4122_, v_i_4121_, v___x_4136_);
v___x_4138_ = ((size_t)1ULL);
v___x_4139_ = lean_usize_add(v_i_4121_, v___x_4138_);
v___x_4140_ = lean_array_uset(v_bs_x27_4137_, v_i_4121_, v_a_4135_);
v_i_4121_ = v___x_4139_;
v_bs_4122_ = v___x_4140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4142_, lean_object* v_i_4143_, lean_object* v_bs_4144_){
_start:
{
size_t v_sz_boxed_4145_; size_t v_i_boxed_4146_; lean_object* v_res_4147_; 
v_sz_boxed_4145_ = lean_unbox_usize(v_sz_4142_);
lean_dec(v_sz_4142_);
v_i_boxed_4146_ = lean_unbox_usize(v_i_4143_);
lean_dec(v_i_4143_);
v_res_4147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4145_, v_i_boxed_4146_, v_bs_4144_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4148_){
_start:
{
if (lean_obj_tag(v_x_4148_) == 4)
{
lean_object* v_elems_4149_; size_t v_sz_4150_; size_t v___x_4151_; lean_object* v___x_4152_; 
v_elems_4149_ = lean_ctor_get(v_x_4148_, 0);
lean_inc_ref(v_elems_4149_);
lean_dec_ref_known(v_x_4148_, 1);
v_sz_4150_ = lean_array_size(v_elems_4149_);
v___x_4151_ = ((size_t)0ULL);
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4150_, v___x_4151_, v_elems_4149_);
return v___x_4152_;
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4153_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4154_ = lean_unsigned_to_nat(80u);
v___x_4155_ = l_Lean_Json_pretty(v_x_4148_, v___x_4154_);
v___x_4156_ = lean_string_append(v___x_4153_, v___x_4155_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4158_ = lean_string_append(v___x_4156_, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4160_, lean_object* v_k_4161_){
_start:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = l_Lean_Json_getObjValD(v_j_4160_, v_k_4161_);
v___x_4163_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4164_, lean_object* v_k_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4164_, v_k_4165_);
lean_dec_ref(v_k_4165_);
return v_res_4166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4173_ = 1;
v___x_4174_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4174_, v___x_4173_);
return v___x_4175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4178_ = lean_string_append(v___x_4177_, v___x_4176_);
return v___x_4178_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = 1;
v___x_4182_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4183_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4182_, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4185_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4186_ = lean_string_append(v___x_4185_, v___x_4184_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4188_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4189_ = lean_string_append(v___x_4188_, v___x_4187_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = 1;
v___x_4194_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4194_, v___x_4193_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4196_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4197_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4198_ = lean_string_append(v___x_4197_, v___x_4196_);
return v___x_4198_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4200_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4201_ = lean_string_append(v___x_4200_, v___x_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4202_);
v___x_4204_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4202_, v___x_4203_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_json_4202_);
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4214_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4214_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4209_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4210_ = lean_string_append(v___x_4209_, v_a_4205_);
lean_dec(v_a_4205_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4210_);
v___x_4212_ = v___x_4207_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_a_4215_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4217_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4202_, v___x_4216_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_a_4215_);
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4227_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4227_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4222_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4223_ = lean_string_append(v___x_4222_, v_a_4218_);
lean_dec(v_a_4218_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4223_);
v___x_4225_ = v___x_4220_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4236_; 
v_a_4228_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4230_ = v___x_4217_;
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4217_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_a_4215_);
lean_ctor_set(v___x_4232_, 1, v_a_4228_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 0, v___x_4232_);
v___x_4234_ = v___x_4230_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_bs_4241_){
_start:
{
uint8_t v___x_4242_; 
v___x_4242_ = lean_usize_dec_lt(v_i_4240_, v_sz_4239_);
if (v___x_4242_ == 0)
{
return v_bs_4241_;
}
else
{
lean_object* v_v_4243_; lean_object* v___x_4244_; lean_object* v_bs_x27_4245_; lean_object* v___x_4246_; size_t v___x_4247_; size_t v___x_4248_; lean_object* v___x_4249_; 
v_v_4243_ = lean_array_uget(v_bs_4241_, v_i_4240_);
v___x_4244_ = lean_unsigned_to_nat(0u);
v_bs_x27_4245_ = lean_array_uset(v_bs_4241_, v_i_4240_, v___x_4244_);
v___x_4246_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4243_);
v___x_4247_ = ((size_t)1ULL);
v___x_4248_ = lean_usize_add(v_i_4240_, v___x_4247_);
v___x_4249_ = lean_array_uset(v_bs_x27_4245_, v_i_4240_, v___x_4246_);
v_i_4240_ = v___x_4248_;
v_bs_4241_ = v___x_4249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4251_, lean_object* v_i_4252_, lean_object* v_bs_4253_){
_start:
{
size_t v_sz_boxed_4254_; size_t v_i_boxed_4255_; lean_object* v_res_4256_; 
v_sz_boxed_4254_ = lean_unbox_usize(v_sz_4251_);
lean_dec(v_sz_4251_);
v_i_boxed_4255_ = lean_unbox_usize(v_i_4252_);
lean_dec(v_i_4252_);
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4254_, v_i_boxed_4255_, v_bs_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4257_){
_start:
{
size_t v_sz_4258_; size_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_sz_4258_ = lean_array_size(v_a_4257_);
v___x_4259_ = ((size_t)0ULL);
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4258_, v___x_4259_, v_a_4257_);
v___x_4261_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4262_){
_start:
{
lean_object* v_sourceRequestID_4263_; lean_object* v_queries_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4302_; 
v_sourceRequestID_4263_ = lean_ctor_get(v_x_4262_, 0);
v_queries_4264_ = lean_ctor_get(v_x_4262_, 1);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4262_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4266_ = v_x_4262_;
v_isShared_4267_ = v_isSharedCheck_4302_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_queries_4264_);
lean_inc(v_sourceRequestID_4263_);
lean_dec(v_x_4262_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4302_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___y_4270_; 
v___x_4268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4263_))
{
case 0:
{
lean_object* v_s_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_s_4285_ = lean_ctor_get(v_sourceRequestID_4263_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v_sourceRequestID_4263_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v_sourceRequestID_4263_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_s_4285_);
lean_dec(v_sourceRequestID_4263_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
lean_ctor_set_tag(v___x_4287_, 3);
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_s_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
v___y_4270_ = v___x_4290_;
goto v___jp_4269_;
}
}
}
case 1:
{
lean_object* v_n_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_n_4293_ = lean_ctor_get(v_sourceRequestID_4263_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_sourceRequestID_4263_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v_sourceRequestID_4263_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_n_4293_);
lean_dec(v_sourceRequestID_4263_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set_tag(v___x_4295_, 2);
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_n_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
v___y_4270_ = v___x_4298_;
goto v___jp_4269_;
}
}
}
default: 
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_box(0);
v___y_4270_ = v___x_4301_;
goto v___jp_4269_;
}
}
v___jp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v___y_4270_);
lean_ctor_set(v___x_4266_, 0, v___x_4268_);
v___x_4272_ = v___x_4266_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v___y_4270_);
v___x_4272_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4273_ = lean_box(0);
v___x_4274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4276_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4264_);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
lean_ctor_set(v___x_4278_, 1, v___x_4273_);
v___x_4279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
lean_ctor_set(v___x_4279_, 1, v___x_4273_);
v___x_4280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4274_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4282_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4280_, v___x_4281_);
v___x_4283_ = l_Lean_Json_mkObj(v___x_4282_);
lean_dec(v___x_4282_);
return v___x_4283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4305_, lean_object* v_k_4306_){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = l_Lean_Json_getObjValD(v_j_4305_, v_k_4306_);
v___x_4308_ = l_Lean_Name_fromJson_x3f(v___x_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4309_, lean_object* v_k_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4309_, v_k_4310_);
lean_dec_ref(v_k_4310_);
return v_res_4311_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4318_ = 1;
v___x_4319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4319_, v___x_4318_);
return v___x_4320_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4322_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4323_ = lean_string_append(v___x_4322_, v___x_4321_);
return v___x_4323_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4326_ = 1;
v___x_4327_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4327_, v___x_4326_);
return v___x_4328_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4331_ = lean_string_append(v___x_4330_, v___x_4329_);
return v___x_4331_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4333_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4334_ = lean_string_append(v___x_4333_, v___x_4332_);
return v___x_4334_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = 1;
v___x_4339_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4339_, v___x_4338_);
return v___x_4340_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4342_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4343_ = lean_string_append(v___x_4342_, v___x_4341_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4344_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4345_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4346_ = lean_string_append(v___x_4345_, v___x_4344_);
return v___x_4346_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4350_ = 1;
v___x_4351_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4351_, v___x_4350_);
return v___x_4352_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4354_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4355_ = lean_string_append(v___x_4354_, v___x_4353_);
return v___x_4355_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4357_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4358_ = lean_string_append(v___x_4357_, v___x_4356_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4359_){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4359_);
v___x_4361_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4359_, v___x_4360_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4371_; 
lean_dec(v_json_4359_);
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4371_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4366_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4367_ = lean_string_append(v___x_4366_, v_a_4362_);
lean_dec(v_a_4362_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4367_);
v___x_4369_ = v___x_4364_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_a_4372_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4361_, 1);
v___x_4373_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4359_);
v___x_4374_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4359_, v___x_4373_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_a_4372_);
lean_dec(v_json_4359_);
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4384_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
v___x_4379_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4380_ = lean_string_append(v___x_4379_, v_a_4375_);
lean_dec(v_a_4375_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 0, v___x_4380_);
v___x_4382_ = v___x_4377_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_a_4385_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4386_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4387_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4359_, v___x_4386_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_a_4385_);
lean_dec(v_a_4372_);
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4397_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4397_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4392_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4393_ = lean_string_append(v___x_4392_, v_a_4388_);
lean_dec(v_a_4388_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4393_);
v___x_4395_ = v___x_4390_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4407_; 
v_a_4398_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4400_ = v___x_4387_;
v_isShared_4401_ = v_isSharedCheck_4407_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4387_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4407_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; uint8_t v___x_4403_; lean_object* v___x_4405_; 
v___x_4402_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4402_, 0, v_a_4372_);
lean_ctor_set(v___x_4402_, 1, v_a_4385_);
v___x_4403_ = lean_unbox(v_a_4398_);
lean_dec(v_a_4398_);
lean_ctor_set_uint8(v___x_4402_, sizeof(void*)*2, v___x_4403_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 0, v___x_4402_);
v___x_4405_ = v___x_4400_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4402_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4410_){
_start:
{
lean_object* v_module_4411_; lean_object* v_decl_4412_; uint8_t v_isExactMatch_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_module_4411_ = lean_ctor_get(v_x_4410_, 0);
lean_inc(v_module_4411_);
v_decl_4412_ = lean_ctor_get(v_x_4410_, 1);
lean_inc(v_decl_4412_);
v_isExactMatch_4413_ = lean_ctor_get_uint8(v_x_4410_, sizeof(void*)*2);
lean_dec_ref(v_x_4410_);
v___x_4414_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4415_ = 1;
v___x_4416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4411_, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4414_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = lean_box(0);
v___x_4420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4412_, v___x_4415_);
v___x_4423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4421_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
v___x_4425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v___x_4419_);
v___x_4426_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4427_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4427_, 0, v_isExactMatch_4413_);
v___x_4428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4426_);
lean_ctor_set(v___x_4428_, 1, v___x_4427_);
v___x_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
lean_ctor_set(v___x_4429_, 1, v___x_4419_);
v___x_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
lean_ctor_set(v___x_4430_, 1, v___x_4419_);
v___x_4431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4425_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4420_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4434_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4432_, v___x_4433_);
v___x_4435_ = l_Lean_Json_mkObj(v___x_4434_);
lean_dec(v___x_4434_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4438_, size_t v_i_4439_, lean_object* v_bs_4440_){
_start:
{
uint8_t v___x_4441_; 
v___x_4441_ = lean_usize_dec_lt(v_i_4439_, v_sz_4438_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; 
v___x_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4442_, 0, v_bs_4440_);
return v___x_4442_;
}
else
{
lean_object* v_v_4443_; lean_object* v___x_4444_; 
v_v_4443_ = lean_array_uget_borrowed(v_bs_4440_, v_i_4439_);
lean_inc(v_v_4443_);
v___x_4444_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4443_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec_ref(v_bs_4440_);
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4454_; lean_object* v_bs_x27_4455_; size_t v___x_4456_; size_t v___x_4457_; lean_object* v___x_4458_; 
v_a_4453_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4444_, 1);
v___x_4454_ = lean_unsigned_to_nat(0u);
v_bs_x27_4455_ = lean_array_uset(v_bs_4440_, v_i_4439_, v___x_4454_);
v___x_4456_ = ((size_t)1ULL);
v___x_4457_ = lean_usize_add(v_i_4439_, v___x_4456_);
v___x_4458_ = lean_array_uset(v_bs_x27_4455_, v_i_4439_, v_a_4453_);
v_i_4439_ = v___x_4457_;
v_bs_4440_ = v___x_4458_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4460_, lean_object* v_i_4461_, lean_object* v_bs_4462_){
_start:
{
size_t v_sz_boxed_4463_; size_t v_i_boxed_4464_; lean_object* v_res_4465_; 
v_sz_boxed_4463_ = lean_unbox_usize(v_sz_4460_);
lean_dec(v_sz_4460_);
v_i_boxed_4464_ = lean_unbox_usize(v_i_4461_);
lean_dec(v_i_4461_);
v_res_4465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4463_, v_i_boxed_4464_, v_bs_4462_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4466_){
_start:
{
if (lean_obj_tag(v_x_4466_) == 4)
{
lean_object* v_elems_4467_; size_t v_sz_4468_; size_t v___x_4469_; lean_object* v___x_4470_; 
v_elems_4467_ = lean_ctor_get(v_x_4466_, 0);
lean_inc_ref(v_elems_4467_);
lean_dec_ref_known(v_x_4466_, 1);
v_sz_4468_ = lean_array_size(v_elems_4467_);
v___x_4469_ = ((size_t)0ULL);
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4468_, v___x_4469_, v_elems_4467_);
return v___x_4470_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4471_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4472_ = lean_unsigned_to_nat(80u);
v___x_4473_ = l_Lean_Json_pretty(v_x_4466_, v___x_4472_);
v___x_4474_ = lean_string_append(v___x_4471_, v___x_4473_);
lean_dec_ref(v___x_4473_);
v___x_4475_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4476_ = lean_string_append(v___x_4474_, v___x_4475_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4478_, size_t v_i_4479_, lean_object* v_bs_4480_){
_start:
{
uint8_t v___x_4481_; 
v___x_4481_ = lean_usize_dec_lt(v_i_4479_, v_sz_4478_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4482_, 0, v_bs_4480_);
return v___x_4482_;
}
else
{
lean_object* v_v_4483_; lean_object* v___x_4484_; 
v_v_4483_ = lean_array_uget_borrowed(v_bs_4480_, v_i_4479_);
lean_inc(v_v_4483_);
v___x_4484_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4483_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref(v_bs_4480_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4494_; lean_object* v_bs_x27_4495_; size_t v___x_4496_; size_t v___x_4497_; lean_object* v___x_4498_; 
v_a_4493_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v___x_4484_, 1);
v___x_4494_ = lean_unsigned_to_nat(0u);
v_bs_x27_4495_ = lean_array_uset(v_bs_4480_, v_i_4479_, v___x_4494_);
v___x_4496_ = ((size_t)1ULL);
v___x_4497_ = lean_usize_add(v_i_4479_, v___x_4496_);
v___x_4498_ = lean_array_uset(v_bs_x27_4495_, v_i_4479_, v_a_4493_);
v_i_4479_ = v___x_4497_;
v_bs_4480_ = v___x_4498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4500_, lean_object* v_i_4501_, lean_object* v_bs_4502_){
_start:
{
size_t v_sz_boxed_4503_; size_t v_i_boxed_4504_; lean_object* v_res_4505_; 
v_sz_boxed_4503_ = lean_unbox_usize(v_sz_4500_);
lean_dec(v_sz_4500_);
v_i_boxed_4504_ = lean_unbox_usize(v_i_4501_);
lean_dec(v_i_4501_);
v_res_4505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4503_, v_i_boxed_4504_, v_bs_4502_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4506_){
_start:
{
if (lean_obj_tag(v_x_4506_) == 4)
{
lean_object* v_elems_4507_; size_t v_sz_4508_; size_t v___x_4509_; lean_object* v___x_4510_; 
v_elems_4507_ = lean_ctor_get(v_x_4506_, 0);
lean_inc_ref(v_elems_4507_);
lean_dec_ref_known(v_x_4506_, 1);
v_sz_4508_ = lean_array_size(v_elems_4507_);
v___x_4509_ = ((size_t)0ULL);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4508_, v___x_4509_, v_elems_4507_);
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4511_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4512_ = lean_unsigned_to_nat(80u);
v___x_4513_ = l_Lean_Json_pretty(v_x_4506_, v___x_4512_);
v___x_4514_ = lean_string_append(v___x_4511_, v___x_4513_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4516_ = lean_string_append(v___x_4514_, v___x_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4518_, lean_object* v_k_4519_){
_start:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = l_Lean_Json_getObjValD(v_j_4518_, v_k_4519_);
v___x_4521_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4522_, lean_object* v_k_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4522_, v_k_4523_);
lean_dec_ref(v_k_4523_);
return v_res_4524_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = 1;
v___x_4532_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4532_, v___x_4531_);
return v___x_4533_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4536_ = lean_string_append(v___x_4535_, v___x_4534_);
return v___x_4536_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = 1;
v___x_4540_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4540_, v___x_4539_);
return v___x_4541_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4544_ = lean_string_append(v___x_4543_, v___x_4542_);
return v___x_4544_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4546_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4547_ = lean_string_append(v___x_4546_, v___x_4545_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4548_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4550_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4548_, v___x_4549_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4560_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4553_ = v___x_4550_;
v_isShared_4554_ = v_isSharedCheck_4560_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4550_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4560_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4556_ = lean_string_append(v___x_4555_, v_a_4551_);
lean_dec(v_a_4551_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4556_);
v___x_4558_ = v___x_4553_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
v_a_4561_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4550_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4550_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4571_, size_t v_i_4572_, lean_object* v_bs_4573_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_usize_dec_lt(v_i_4572_, v_sz_4571_);
if (v___x_4574_ == 0)
{
return v_bs_4573_;
}
else
{
lean_object* v_v_4575_; lean_object* v___x_4576_; lean_object* v_bs_x27_4577_; lean_object* v___x_4578_; size_t v___x_4579_; size_t v___x_4580_; lean_object* v___x_4581_; 
v_v_4575_ = lean_array_uget(v_bs_4573_, v_i_4572_);
v___x_4576_ = lean_unsigned_to_nat(0u);
v_bs_x27_4577_ = lean_array_uset(v_bs_4573_, v_i_4572_, v___x_4576_);
v___x_4578_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4575_);
v___x_4579_ = ((size_t)1ULL);
v___x_4580_ = lean_usize_add(v_i_4572_, v___x_4579_);
v___x_4581_ = lean_array_uset(v_bs_x27_4577_, v_i_4572_, v___x_4578_);
v_i_4572_ = v___x_4580_;
v_bs_4573_ = v___x_4581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4583_, lean_object* v_i_4584_, lean_object* v_bs_4585_){
_start:
{
size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4583_);
lean_dec(v_sz_4583_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4584_);
lean_dec(v_i_4584_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4586_, v_i_boxed_4587_, v_bs_4585_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4589_){
_start:
{
size_t v_sz_4590_; size_t v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_sz_4590_ = lean_array_size(v_a_4589_);
v___x_4591_ = ((size_t)0ULL);
v___x_4592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4590_, v___x_4591_, v_a_4589_);
v___x_4593_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4594_, size_t v_i_4595_, lean_object* v_bs_4596_){
_start:
{
uint8_t v___x_4597_; 
v___x_4597_ = lean_usize_dec_lt(v_i_4595_, v_sz_4594_);
if (v___x_4597_ == 0)
{
return v_bs_4596_;
}
else
{
lean_object* v_v_4598_; lean_object* v___x_4599_; lean_object* v_bs_x27_4600_; lean_object* v___x_4601_; size_t v___x_4602_; size_t v___x_4603_; lean_object* v___x_4604_; 
v_v_4598_ = lean_array_uget(v_bs_4596_, v_i_4595_);
v___x_4599_ = lean_unsigned_to_nat(0u);
v_bs_x27_4600_ = lean_array_uset(v_bs_4596_, v_i_4595_, v___x_4599_);
v___x_4601_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4598_);
v___x_4602_ = ((size_t)1ULL);
v___x_4603_ = lean_usize_add(v_i_4595_, v___x_4602_);
v___x_4604_ = lean_array_uset(v_bs_x27_4600_, v_i_4595_, v___x_4601_);
v_i_4595_ = v___x_4603_;
v_bs_4596_ = v___x_4604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4606_, lean_object* v_i_4607_, lean_object* v_bs_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4606_);
lean_dec(v_sz_4606_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4607_);
lean_dec(v_i_4607_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4609_, v_i_boxed_4610_, v_bs_4608_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4612_){
_start:
{
size_t v_sz_4613_; size_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v_sz_4613_ = lean_array_size(v_a_4612_);
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4613_, v___x_4614_, v_a_4612_);
v___x_4616_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4617_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4619_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4617_);
v___x_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4618_);
lean_ctor_set(v___x_4620_, 1, v___x_4619_);
v___x_4621_ = lean_box(0);
v___x_4622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4620_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
v___x_4623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
lean_ctor_set(v___x_4623_, 1, v___x_4621_);
v___x_4624_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4625_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4623_, v___x_4624_);
v___x_4626_ = l_Lean_Json_mkObj(v___x_4625_);
lean_dec(v___x_4625_);
return v___x_4626_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = 1;
v___x_4639_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4639_, v___x_4638_);
return v___x_4640_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4642_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4643_ = lean_string_append(v___x_4642_, v___x_4641_);
return v___x_4643_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4645_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4646_ = lean_string_append(v___x_4645_, v___x_4644_);
return v___x_4646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4648_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4649_ = lean_string_append(v___x_4648_, v___x_4647_);
return v___x_4649_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4650_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4651_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4652_ = lean_string_append(v___x_4651_, v___x_4650_);
return v___x_4652_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4653_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4654_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4655_ = lean_string_append(v___x_4654_, v___x_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4656_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4656_);
v___x_4658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4656_, v___x_4657_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4668_; 
lean_dec(v_json_4656_);
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4668_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4668_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4664_ = lean_string_append(v___x_4663_, v_a_4659_);
lean_dec(v_a_4659_);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4664_);
v___x_4666_ = v___x_4661_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_a_4669_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4658_, 1);
v___x_4670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4656_, v___x_4670_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v_a_4669_);
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4681_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4681_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4677_ = lean_string_append(v___x_4676_, v_a_4672_);
lean_dec(v_a_4672_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4677_);
v___x_4679_ = v___x_4674_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4690_; 
v_a_4682_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4684_ = v___x_4671_;
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4671_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4686_, 0, v_a_4669_);
lean_ctor_set(v___x_4686_, 1, v_a_4682_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4686_);
v___x_4688_ = v___x_4684_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4686_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4693_){
_start:
{
lean_object* v_module_4694_; lean_object* v_decl_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4718_; 
v_module_4694_ = lean_ctor_get(v_x_4693_, 0);
v_decl_4695_ = lean_ctor_get(v_x_4693_, 1);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_x_4693_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4697_ = v_x_4693_;
v_isShared_4698_ = v_isSharedCheck_4718_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_decl_4695_);
lean_inc(v_module_4694_);
lean_dec(v_x_4693_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4718_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; uint8_t v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4704_; 
v___x_4699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4700_ = 1;
v___x_4701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4694_, v___x_4700_);
v___x_4702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v___x_4702_);
lean_ctor_set(v___x_4697_, 0, v___x_4699_);
v___x_4704_ = v___x_4697_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4699_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4702_);
v___x_4704_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4705_ = lean_box(0);
v___x_4706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4704_);
lean_ctor_set(v___x_4706_, 1, v___x_4705_);
v___x_4707_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4708_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4695_, v___x_4700_);
v___x_4709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4707_);
lean_ctor_set(v___x_4710_, 1, v___x_4709_);
v___x_4711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4710_);
lean_ctor_set(v___x_4711_, 1, v___x_4705_);
v___x_4712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
lean_ctor_set(v___x_4712_, 1, v___x_4705_);
v___x_4713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4706_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
v___x_4714_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4715_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4713_, v___x_4714_);
v___x_4716_ = l_Lean_Json_mkObj(v___x_4715_);
lean_dec(v___x_4715_);
return v___x_4716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4721_, lean_object* v_k_4722_){
_start:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4723_ = l_Lean_Json_getObjValD(v_j_4721_, v_k_4722_);
v___x_4724_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4725_, lean_object* v_k_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4725_, v_k_4726_);
lean_dec_ref(v_k_4726_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4730_){
_start:
{
if (lean_obj_tag(v_x_4730_) == 0)
{
lean_object* v___x_4731_; 
v___x_4731_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4731_;
}
else
{
lean_object* v___x_4732_; 
v___x_4732_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4730_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4732_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4749_; 
v_a_4741_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4743_ = v___x_4732_;
v_isShared_4744_ = v_isSharedCheck_4749_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4732_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4749_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4745_, 0, v_a_4741_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4745_);
v___x_4747_ = v___x_4743_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4750_, lean_object* v_k_4751_){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = l_Lean_Json_getObjValD(v_j_4750_, v_k_4751_);
v___x_4753_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4754_, lean_object* v_k_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4754_, v_k_4755_);
lean_dec_ref(v_k_4755_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4759_){
_start:
{
if (lean_obj_tag(v_x_4759_) == 0)
{
lean_object* v___x_4760_; 
v___x_4760_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4760_;
}
else
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4759_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4761_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4778_; 
v_a_4770_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4772_ = v___x_4761_;
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4761_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4774_, 0, v_a_4770_);
if (v_isShared_4773_ == 0)
{
lean_ctor_set(v___x_4772_, 0, v___x_4774_);
v___x_4776_ = v___x_4772_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4779_, lean_object* v_k_4780_){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = l_Lean_Json_getObjValD(v_j_4779_, v_k_4780_);
v___x_4782_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4781_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4783_, lean_object* v_k_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4783_, v_k_4784_);
lean_dec_ref(v_k_4784_);
return v_res_4785_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = 1;
v___x_4793_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4794_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4793_, v___x_4792_);
return v___x_4794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4797_ = lean_string_append(v___x_4796_, v___x_4795_);
return v___x_4797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = 1;
v___x_4802_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4802_, v___x_4801_);
return v___x_4803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4805_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4806_ = lean_string_append(v___x_4805_, v___x_4804_);
return v___x_4806_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4808_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4809_ = lean_string_append(v___x_4808_, v___x_4807_);
return v___x_4809_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = 1;
v___x_4814_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4814_, v___x_4813_);
return v___x_4815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4816_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4818_ = lean_string_append(v___x_4817_, v___x_4816_);
return v___x_4818_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4819_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4821_ = lean_string_append(v___x_4820_, v___x_4819_);
return v___x_4821_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4825_ = 1;
v___x_4826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4826_, v___x_4825_);
return v___x_4827_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4828_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4829_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4830_ = lean_string_append(v___x_4829_, v___x_4828_);
return v___x_4830_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4831_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4833_ = lean_string_append(v___x_4832_, v___x_4831_);
return v___x_4833_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = 1;
v___x_4838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4838_, v___x_4837_);
return v___x_4839_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4842_ = lean_string_append(v___x_4841_, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4845_ = lean_string_append(v___x_4844_, v___x_4843_);
return v___x_4845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4850_ = 1;
v___x_4851_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_4852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4851_, v___x_4850_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_4854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4855_ = lean_string_append(v___x_4854_, v___x_4853_);
return v___x_4855_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4857_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_4858_ = lean_string_append(v___x_4857_, v___x_4856_);
return v___x_4858_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = 1;
v___x_4863_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_4864_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4863_, v___x_4862_);
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_4866_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4867_ = lean_string_append(v___x_4866_, v___x_4865_);
return v___x_4867_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4869_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_4870_ = lean_string_append(v___x_4869_, v___x_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_4871_){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_4871_);
v___x_4873_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_4871_, v___x_4872_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4883_; 
lean_dec(v_json_4871_);
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4883_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4883_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4878_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_4879_ = lean_string_append(v___x_4878_, v_a_4874_);
lean_dec(v_a_4874_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4879_);
v___x_4881_ = v___x_4876_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_a_4884_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4873_, 1);
v___x_4885_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_4871_);
v___x_4886_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4871_, v___x_4885_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4896_; 
lean_dec(v_a_4884_);
lean_dec(v_json_4871_);
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4896_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4896_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4891_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_4892_ = lean_string_append(v___x_4891_, v_a_4887_);
lean_dec(v_a_4887_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4892_);
v___x_4894_ = v___x_4889_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
v_a_4897_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4886_, 1);
v___x_4898_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_4871_);
v___x_4899_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4871_, v___x_4898_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4909_; 
lean_dec(v_a_4897_);
lean_dec(v_a_4884_);
lean_dec(v_json_4871_);
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4904_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_4905_ = lean_string_append(v___x_4904_, v_a_4900_);
lean_dec(v_a_4900_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4905_);
v___x_4907_ = v___x_4902_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v_a_4910_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___x_4899_, 1);
v___x_4911_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_4871_);
v___x_4912_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4871_, v___x_4911_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4922_; 
lean_dec(v_a_4910_);
lean_dec(v_a_4897_);
lean_dec(v_a_4884_);
lean_dec(v_json_4871_);
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4922_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4922_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4917_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_4918_ = lean_string_append(v___x_4917_, v_a_4913_);
lean_dec(v_a_4913_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4918_);
v___x_4920_ = v___x_4915_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v_a_4923_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4924_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_4871_);
v___x_4925_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_4871_, v___x_4924_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4935_; 
lean_dec(v_a_4923_);
lean_dec(v_a_4910_);
lean_dec(v_a_4897_);
lean_dec(v_a_4884_);
lean_dec(v_json_4871_);
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_4935_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4935_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4930_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_4931_ = lean_string_append(v___x_4930_, v_a_4926_);
lean_dec(v_a_4926_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4931_);
v___x_4933_ = v___x_4928_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v_a_4936_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4936_);
lean_dec_ref_known(v___x_4925_, 1);
v___x_4937_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_4938_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4871_, v___x_4937_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_a_4936_);
lean_dec(v_a_4923_);
lean_dec(v_a_4910_);
lean_dec(v_a_4897_);
lean_dec(v_a_4884_);
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4941_ = v___x_4938_;
v_isShared_4942_ = v_isSharedCheck_4948_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4948_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_4944_ = lean_string_append(v___x_4943_, v_a_4939_);
lean_dec(v_a_4939_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4944_);
v___x_4946_ = v___x_4941_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4959_; 
v_a_4949_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4951_ = v___x_4938_;
v_isShared_4952_ = v_isSharedCheck_4959_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4938_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4959_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; uint8_t v___x_4955_; lean_object* v___x_4957_; 
v___x_4953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4953_, 0, v_a_4884_);
lean_ctor_set(v___x_4953_, 1, v_a_4897_);
lean_ctor_set(v___x_4953_, 2, v_a_4910_);
lean_ctor_set(v___x_4953_, 3, v_a_4923_);
v___x_4954_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
lean_ctor_set(v___x_4954_, 1, v_a_4936_);
v___x_4955_ = lean_unbox(v_a_4949_);
lean_dec(v_a_4949_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*2, v___x_4955_);
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 0, v___x_4954_);
v___x_4957_ = v___x_4951_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v___x_4954_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_4962_, lean_object* v_x_4963_){
_start:
{
if (lean_obj_tag(v_x_4963_) == 0)
{
lean_object* v___x_4964_; 
lean_dec_ref(v_k_4962_);
v___x_4964_ = lean_box(0);
return v___x_4964_;
}
else
{
lean_object* v_val_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v_val_4965_ = lean_ctor_get(v_x_4963_, 0);
lean_inc(v_val_4965_);
lean_dec_ref_known(v_x_4963_, 1);
v___x_4966_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_4965_);
v___x_4967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4967_, 0, v_k_4962_);
lean_ctor_set(v___x_4967_, 1, v___x_4966_);
v___x_4968_ = lean_box(0);
v___x_4969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4967_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_4970_, lean_object* v_x_4971_){
_start:
{
if (lean_obj_tag(v_x_4971_) == 0)
{
lean_object* v___x_4972_; 
lean_dec_ref(v_k_4970_);
v___x_4972_ = lean_box(0);
return v___x_4972_;
}
else
{
lean_object* v_val_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v_val_4973_ = lean_ctor_get(v_x_4971_, 0);
lean_inc(v_val_4973_);
lean_dec_ref_known(v_x_4971_, 1);
v___x_4974_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_4973_);
v___x_4975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4975_, 0, v_k_4970_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = lean_box(0);
v___x_4977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4975_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
return v___x_4977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_4978_){
_start:
{
lean_object* v_toLocationLink_4979_; lean_object* v_ident_x3f_4980_; uint8_t v_isDefault_4981_; lean_object* v_originSelectionRange_x3f_4982_; lean_object* v_targetUri_4983_; lean_object* v_targetRange_4984_; lean_object* v_targetSelectionRange_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v_toLocationLink_4979_ = lean_ctor_get(v_x_4978_, 0);
lean_inc_ref(v_toLocationLink_4979_);
v_ident_x3f_4980_ = lean_ctor_get(v_x_4978_, 1);
lean_inc(v_ident_x3f_4980_);
v_isDefault_4981_ = lean_ctor_get_uint8(v_x_4978_, sizeof(void*)*2);
lean_dec_ref(v_x_4978_);
v_originSelectionRange_x3f_4982_ = lean_ctor_get(v_toLocationLink_4979_, 0);
lean_inc(v_originSelectionRange_x3f_4982_);
v_targetUri_4983_ = lean_ctor_get(v_toLocationLink_4979_, 1);
lean_inc_ref(v_targetUri_4983_);
v_targetRange_4984_ = lean_ctor_get(v_toLocationLink_4979_, 2);
lean_inc_ref(v_targetRange_4984_);
v_targetSelectionRange_4985_ = lean_ctor_get(v_toLocationLink_4979_, 3);
lean_inc_ref(v_targetSelectionRange_4985_);
lean_dec_ref(v_toLocationLink_4979_);
v___x_4986_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_4987_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_4986_, v_originSelectionRange_x3f_4982_);
v___x_4988_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_4989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4989_, 0, v_targetUri_4983_);
v___x_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = lean_box(0);
v___x_4992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_4994_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_4984_);
v___x_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4993_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4995_);
lean_ctor_set(v___x_4996_, 1, v___x_4991_);
v___x_4997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_4998_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_4985_);
v___x_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v___x_4991_);
v___x_5001_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5002_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5001_, v_ident_x3f_4980_);
v___x_5003_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5004_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5004_, 0, v_isDefault_4981_);
v___x_5005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5003_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
lean_ctor_set(v___x_5006_, 1, v___x_4991_);
v___x_5007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5006_);
lean_ctor_set(v___x_5007_, 1, v___x_4991_);
v___x_5008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5002_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
v___x_5009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5000_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_4996_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5011_, 0, v___x_4992_);
lean_ctor_set(v___x_5011_, 1, v___x_5010_);
v___x_5012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_4987_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5014_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5012_, v___x_5013_);
v___x_5015_ = l_Lean_Json_mkObj(v___x_5014_);
lean_dec(v___x_5014_);
return v___x_5015_;
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

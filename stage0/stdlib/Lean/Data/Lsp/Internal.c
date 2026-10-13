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
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_json_1810_);
v_a_1823_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1812_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1812_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 0);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1810_);
v___x_1833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1810_, v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1831_);
lean_dec(v_json_1810_);
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
v___x_1838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
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
lean_dec(v_a_1831_);
lean_dec(v_json_1810_);
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
lean_dec_ref_known(v___x_1833_, 1);
v___x_1853_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1810_, v___x_1853_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1852_);
lean_dec(v_a_1831_);
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
v___x_1859_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
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
lean_dec(v_a_1831_);
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
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
v_a_1873_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1875_ = v___x_1854_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1854_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1877_, 0, v_a_1831_);
lean_ctor_set(v___x_1877_, 1, v_a_1873_);
v___x_1878_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*2, v___x_1878_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1877_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1877_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1885_, size_t v_i_1886_, lean_object* v_bs_1887_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_usize_dec_lt(v_i_1886_, v_sz_1885_);
if (v___x_1888_ == 0)
{
return v_bs_1887_;
}
else
{
lean_object* v_v_1889_; lean_object* v_module_1890_; uint8_t v_isPrivate_1891_; uint8_t v_isAll_1892_; uint8_t v_isMeta_1893_; lean_object* v___x_1894_; lean_object* v_bs_x27_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v_v_1889_ = lean_array_uget_borrowed(v_bs_1887_, v_i_1886_);
v_module_1890_ = lean_ctor_get(v_v_1889_, 0);
lean_inc_ref(v_module_1890_);
v_isPrivate_1891_ = lean_ctor_get_uint8(v_v_1889_, sizeof(void*)*1);
v_isAll_1892_ = lean_ctor_get_uint8(v_v_1889_, sizeof(void*)*1 + 1);
v_isMeta_1893_ = lean_ctor_get_uint8(v_v_1889_, sizeof(void*)*1 + 2);
v___x_1894_ = lean_unsigned_to_nat(0u);
v_bs_x27_1895_ = lean_array_uset(v_bs_1887_, v_i_1886_, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_module_1890_);
v___x_1897_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1897_, 0, v_isPrivate_1891_);
v___x_1898_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1898_, 0, v_isAll_1892_);
v___x_1899_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1899_, 0, v_isMeta_1893_);
v___x_1900_ = lean_unsigned_to_nat(4u);
v___x_1901_ = lean_mk_empty_array_with_capacity(v___x_1900_);
v___x_1902_ = lean_array_push(v___x_1901_, v___x_1896_);
v___x_1903_ = lean_array_push(v___x_1902_, v___x_1897_);
v___x_1904_ = lean_array_push(v___x_1903_, v___x_1898_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1899_);
v___x_1906_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_add(v_i_1886_, v___x_1907_);
v___x_1909_ = lean_array_uset(v_bs_x27_1895_, v_i_1886_, v___x_1906_);
v_i_1886_ = v___x_1908_;
v_bs_1887_ = v___x_1909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1911_, lean_object* v_i_1912_, lean_object* v_bs_1913_){
_start:
{
size_t v_sz_boxed_1914_; size_t v_i_boxed_1915_; lean_object* v_res_1916_; 
v_sz_boxed_1914_ = lean_unbox_usize(v_sz_1911_);
lean_dec(v_sz_1911_);
v_i_boxed_1915_ = lean_unbox_usize(v_i_1912_);
lean_dec(v_i_1912_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1914_, v_i_boxed_1915_, v_bs_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1917_){
_start:
{
size_t v_sz_1918_; size_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_sz_1918_ = lean_array_size(v_a_1917_);
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1918_, v___x_1919_, v_a_1917_);
v___x_1921_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
if (lean_obj_tag(v_a_1922_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_array_to_list(v_a_1923_);
return v___x_1924_;
}
else
{
lean_object* v_head_1925_; lean_object* v_tail_1926_; lean_object* v___x_1927_; 
v_head_1925_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_head_1925_);
v_tail_1926_ = lean_ctor_get(v_a_1922_, 1);
lean_inc(v_tail_1926_);
lean_dec_ref_known(v_a_1922_, 2);
v___x_1927_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1923_, v_head_1925_);
v_a_1922_ = v_tail_1926_;
v_a_1923_ = v___x_1927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1931_){
_start:
{
lean_object* v_version_1932_; uint8_t v_isSetupFailure_1933_; lean_object* v_directImports_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_version_1932_ = lean_ctor_get(v_x_1931_, 0);
lean_inc(v_version_1932_);
v_isSetupFailure_1933_ = lean_ctor_get_uint8(v_x_1931_, sizeof(void*)*2);
v_directImports_1934_ = lean_ctor_get(v_x_1931_, 1);
lean_inc_ref(v_directImports_1934_);
lean_dec_ref(v_x_1931_);
v___x_1935_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1936_ = l_Lean_JsonNumber_fromNat(v_version_1932_);
v___x_1937_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1942_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1942_, 0, v_isSetupFailure_1933_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___x_1939_);
v___x_1945_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1946_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1934_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1939_);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v___x_1939_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1944_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1940_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1953_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1951_, v___x_1952_);
v___x_1954_ = l_Lean_Json_mkObj(v___x_1953_);
lean_dec(v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1957_, lean_object* v_v_1958_, lean_object* v_t_1959_){
_start:
{
if (lean_obj_tag(v_t_1959_) == 0)
{
lean_object* v_size_1960_; lean_object* v_k_1961_; lean_object* v_v_1962_; lean_object* v_l_1963_; lean_object* v_r_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2244_; 
v_size_1960_ = lean_ctor_get(v_t_1959_, 0);
v_k_1961_ = lean_ctor_get(v_t_1959_, 1);
v_v_1962_ = lean_ctor_get(v_t_1959_, 2);
v_l_1963_ = lean_ctor_get(v_t_1959_, 3);
v_r_1964_ = lean_ctor_get(v_t_1959_, 4);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_t_1959_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_1966_ = v_t_1959_;
v_isShared_1967_ = v_isSharedCheck_2244_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_r_1964_);
lean_inc(v_l_1963_);
lean_inc(v_v_1962_);
lean_inc(v_k_1961_);
lean_inc(v_size_1960_);
lean_dec(v_t_1959_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2244_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_string_compare(v_k_1957_, v_k_1961_);
switch(v___x_1968_)
{
case 0:
{
lean_object* v_impl_1969_; lean_object* v___x_1970_; 
lean_dec(v_size_1960_);
v_impl_1969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1957_, v_v_1958_, v_l_1963_);
v___x_1970_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1964_) == 0)
{
lean_object* v_size_1971_; lean_object* v_size_1972_; lean_object* v_k_1973_; lean_object* v_v_1974_; lean_object* v_l_1975_; lean_object* v_r_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_size_1971_ = lean_ctor_get(v_r_1964_, 0);
v_size_1972_ = lean_ctor_get(v_impl_1969_, 0);
v_k_1973_ = lean_ctor_get(v_impl_1969_, 1);
v_v_1974_ = lean_ctor_get(v_impl_1969_, 2);
v_l_1975_ = lean_ctor_get(v_impl_1969_, 3);
v_r_1976_ = lean_ctor_get(v_impl_1969_, 4);
lean_inc(v_r_1976_);
v___x_1977_ = lean_unsigned_to_nat(3u);
v___x_1978_ = lean_nat_mul(v___x_1977_, v_size_1971_);
v___x_1979_ = lean_nat_dec_lt(v___x_1978_, v_size_1972_);
lean_dec(v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_dec(v_r_1976_);
v___x_1980_ = lean_nat_add(v___x_1970_, v_size_1972_);
v___x_1981_ = lean_nat_add(v___x_1980_, v_size_1971_);
lean_dec(v___x_1980_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 3, v_impl_1969_);
lean_ctor_set(v___x_1966_, 0, v___x_1981_);
v___x_1983_ = v___x_1966_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_impl_1969_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v_r_1964_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
else
{
lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2050_; 
lean_inc(v_l_1975_);
lean_inc(v_v_1974_);
lean_inc(v_k_1973_);
lean_inc(v_size_1972_);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_impl_1969_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2051_ = lean_ctor_get(v_impl_1969_, 4);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v_impl_1969_, 3);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_impl_1969_, 2);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_impl_1969_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_impl_1969_, 0);
lean_dec(v_unused_2055_);
v___x_1986_ = v_impl_1969_;
v_isShared_1987_ = v_isSharedCheck_2050_;
goto v_resetjp_1985_;
}
else
{
lean_dec(v_impl_1969_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2050_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_size_1988_; lean_object* v_size_1989_; lean_object* v_k_1990_; lean_object* v_v_1991_; lean_object* v_l_1992_; lean_object* v_r_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_size_1988_ = lean_ctor_get(v_l_1975_, 0);
v_size_1989_ = lean_ctor_get(v_r_1976_, 0);
v_k_1990_ = lean_ctor_get(v_r_1976_, 1);
v_v_1991_ = lean_ctor_get(v_r_1976_, 2);
v_l_1992_ = lean_ctor_get(v_r_1976_, 3);
v_r_1993_ = lean_ctor_get(v_r_1976_, 4);
v___x_1994_ = lean_unsigned_to_nat(2u);
v___x_1995_ = lean_nat_mul(v___x_1994_, v_size_1988_);
v___x_1996_ = lean_nat_dec_lt(v_size_1989_, v___x_1995_);
lean_dec(v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2025_; 
lean_inc(v_r_1993_);
lean_inc(v_l_1992_);
lean_inc(v_v_1991_);
lean_inc(v_k_1990_);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_r_1976_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; 
v_unused_2026_ = lean_ctor_get(v_r_1976_, 4);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_r_1976_, 3);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_r_1976_, 2);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_r_1976_, 1);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1976_, 0);
lean_dec(v_unused_2030_);
v___x_1998_ = v_r_1976_;
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_r_1976_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2025_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___x_2013_; lean_object* v___y_2015_; 
v___x_2000_ = lean_nat_add(v___x_1970_, v_size_1972_);
lean_dec(v_size_1972_);
v___x_2001_ = lean_nat_add(v___x_2000_, v_size_1971_);
lean_dec(v___x_2000_);
v___x_2013_ = lean_nat_add(v___x_1970_, v_size_1988_);
if (lean_obj_tag(v_l_1992_) == 0)
{
lean_object* v_size_2023_; 
v_size_2023_ = lean_ctor_get(v_l_1992_, 0);
lean_inc(v_size_2023_);
v___y_2015_ = v_size_2023_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_unsigned_to_nat(0u);
v___y_2015_ = v___x_2024_;
goto v___jp_2014_;
}
v___jp_2002_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_nat_add(v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec(v___y_2004_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 4, v_r_1964_);
lean_ctor_set(v___x_1998_, 3, v_r_1993_);
lean_ctor_set(v___x_1998_, 2, v_v_1962_);
lean_ctor_set(v___x_1998_, 1, v_k_1961_);
lean_ctor_set(v___x_1998_, 0, v___x_2006_);
v___x_2008_ = v___x_1998_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_r_1993_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_r_1964_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 4, v___x_2008_);
lean_ctor_set(v___x_1986_, 3, v___y_2003_);
lean_ctor_set(v___x_1986_, 2, v_v_1991_);
lean_ctor_set(v___x_1986_, 1, v_k_1990_);
lean_ctor_set(v___x_1986_, 0, v___x_2001_);
v___x_2010_ = v___x_1986_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1990_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1991_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v___y_2003_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
v___jp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_nat_add(v___x_2013_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec(v___x_2013_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_l_1992_);
lean_ctor_set(v___x_1966_, 3, v_l_1975_);
lean_ctor_set(v___x_1966_, 2, v_v_1974_);
lean_ctor_set(v___x_1966_, 1, v_k_1973_);
lean_ctor_set(v___x_1966_, 0, v___x_2016_);
v___x_2018_ = v___x_1966_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_k_1973_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_v_1974_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_l_1975_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_l_1992_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_nat_add(v___x_1970_, v_size_1971_);
if (lean_obj_tag(v_r_1993_) == 0)
{
lean_object* v_size_2020_; 
v_size_2020_ = lean_ctor_get(v_r_1993_, 0);
lean_inc(v_size_2020_);
v___y_2003_ = v___x_2018_;
v___y_2004_ = v___x_2019_;
v___y_2005_ = v_size_2020_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_unsigned_to_nat(0u);
v___y_2003_ = v___x_2018_;
v___y_2004_ = v___x_2019_;
v___y_2005_ = v___x_2021_;
goto v___jp_2002_;
}
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_del_object(v___x_1966_);
v___x_2031_ = lean_nat_add(v___x_1970_, v_size_1972_);
lean_dec(v_size_1972_);
v___x_2032_ = lean_nat_add(v___x_2031_, v_size_1971_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_nat_add(v___x_1970_, v_size_1971_);
v___x_2034_ = lean_nat_add(v___x_2033_, v_size_1989_);
lean_dec(v___x_2033_);
lean_inc_ref(v_r_1964_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 4, v_r_1964_);
lean_ctor_set(v___x_1986_, 3, v_r_1976_);
lean_ctor_set(v___x_1986_, 2, v_v_1962_);
lean_ctor_set(v___x_1986_, 1, v_k_1961_);
lean_ctor_set(v___x_1986_, 0, v___x_2034_);
v___x_2036_ = v___x_1986_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_r_1976_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_r_1964_);
v___x_2036_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_isSharedCheck_2043_ = !lean_is_exclusive(v_r_1964_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2044_ = lean_ctor_get(v_r_1964_, 4);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_r_1964_, 3);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_r_1964_, 2);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_r_1964_, 1);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_r_1964_, 0);
lean_dec(v_unused_2048_);
v___x_2038_ = v_r_1964_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v_r_1964_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 4, v___x_2036_);
lean_ctor_set(v___x_2038_, 3, v_l_1975_);
lean_ctor_set(v___x_2038_, 2, v_v_1974_);
lean_ctor_set(v___x_2038_, 1, v_k_1973_);
lean_ctor_set(v___x_2038_, 0, v___x_2032_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_k_1973_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_v_1974_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_l_1975_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___x_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2056_; 
v_l_2056_ = lean_ctor_get(v_impl_1969_, 3);
if (lean_obj_tag(v_l_2056_) == 0)
{
lean_object* v_r_2057_; lean_object* v_k_2058_; lean_object* v_v_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2070_; 
lean_inc_ref(v_l_2056_);
v_r_2057_ = lean_ctor_get(v_impl_1969_, 4);
v_k_2058_ = lean_ctor_get(v_impl_1969_, 1);
v_v_2059_ = lean_ctor_get(v_impl_1969_, 2);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_impl_1969_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2071_ = lean_ctor_get(v_impl_1969_, 3);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_impl_1969_, 0);
lean_dec(v_unused_2072_);
v___x_2061_ = v_impl_1969_;
v_isShared_2062_ = v_isSharedCheck_2070_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_r_2057_);
lean_inc(v_v_2059_);
lean_inc(v_k_2058_);
lean_dec(v_impl_1969_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2070_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2057_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 3, v_r_2057_);
lean_ctor_set(v___x_2061_, 2, v_v_1962_);
lean_ctor_set(v___x_2061_, 1, v_k_1961_);
lean_ctor_set(v___x_2061_, 0, v___x_1970_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_2057_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v___x_2065_);
lean_ctor_set(v___x_1966_, 3, v_l_2056_);
lean_ctor_set(v___x_1966_, 2, v_v_2059_);
lean_ctor_set(v___x_1966_, 1, v_k_2058_);
lean_ctor_set(v___x_1966_, 0, v___x_2063_);
v___x_2067_ = v___x_1966_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_2058_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_2059_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_r_2073_; 
v_r_2073_ = lean_ctor_get(v_impl_1969_, 4);
lean_inc(v_r_2073_);
if (lean_obj_tag(v_r_2073_) == 0)
{
lean_object* v_k_2074_; lean_object* v_v_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2098_; 
lean_inc(v_l_2056_);
v_k_2074_ = lean_ctor_get(v_impl_1969_, 1);
v_v_2075_ = lean_ctor_get(v_impl_1969_, 2);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_impl_1969_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; lean_object* v_unused_2100_; lean_object* v_unused_2101_; 
v_unused_2099_ = lean_ctor_get(v_impl_1969_, 4);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_impl_1969_, 3);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_impl_1969_, 0);
lean_dec(v_unused_2101_);
v___x_2077_ = v_impl_1969_;
v_isShared_2078_ = v_isSharedCheck_2098_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_v_2075_);
lean_inc(v_k_2074_);
lean_dec(v_impl_1969_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2098_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2094_; 
v_k_2079_ = lean_ctor_get(v_r_2073_, 1);
v_v_2080_ = lean_ctor_get(v_r_2073_, 2);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_r_2073_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2095_ = lean_ctor_get(v_r_2073_, 4);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_r_2073_, 3);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_r_2073_, 0);
lean_dec(v_unused_2097_);
v___x_2082_ = v_r_2073_;
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
lean_dec(v_r_2073_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2094_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_unsigned_to_nat(3u);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v_l_2056_);
lean_ctor_set(v___x_2082_, 3, v_l_2056_);
lean_ctor_set(v___x_2082_, 2, v_v_2075_);
lean_ctor_set(v___x_2082_, 1, v_k_2074_);
lean_ctor_set(v___x_2082_, 0, v___x_1970_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_k_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_v_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_l_2056_);
v___x_2086_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 4, v_l_2056_);
lean_ctor_set(v___x_2077_, 2, v_v_1962_);
lean_ctor_set(v___x_2077_, 1, v_k_1961_);
lean_ctor_set(v___x_2077_, 0, v___x_1970_);
v___x_2088_ = v___x_2077_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_l_2056_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v___x_2088_);
lean_ctor_set(v___x_1966_, 3, v___x_2086_);
lean_ctor_set(v___x_1966_, 2, v_v_2080_);
lean_ctor_set(v___x_1966_, 1, v_k_2079_);
lean_ctor_set(v___x_1966_, 0, v___x_2084_);
v___x_2090_ = v___x_1966_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = lean_unsigned_to_nat(2u);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_r_2073_);
lean_ctor_set(v___x_1966_, 3, v_impl_1969_);
lean_ctor_set(v___x_1966_, 0, v___x_2102_);
v___x_2104_ = v___x_1966_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v_impl_1969_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v_r_2073_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2107_; 
lean_dec(v_v_1962_);
lean_dec(v_k_1961_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 2, v_v_1958_);
lean_ctor_set(v___x_1966_, 1, v_k_1957_);
v___x_2107_ = v___x_1966_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_size_1960_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_1957_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_1958_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_r_1964_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
default: 
{
lean_object* v_impl_2109_; lean_object* v___x_2110_; 
lean_dec(v_size_1960_);
v_impl_2109_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1957_, v_v_1958_, v_r_1964_);
v___x_2110_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1963_) == 0)
{
lean_object* v_size_2111_; lean_object* v_size_2112_; lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v_l_2115_; lean_object* v_r_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v_size_2111_ = lean_ctor_get(v_l_1963_, 0);
v_size_2112_ = lean_ctor_get(v_impl_2109_, 0);
v_k_2113_ = lean_ctor_get(v_impl_2109_, 1);
v_v_2114_ = lean_ctor_get(v_impl_2109_, 2);
v_l_2115_ = lean_ctor_get(v_impl_2109_, 3);
lean_inc(v_l_2115_);
v_r_2116_ = lean_ctor_get(v_impl_2109_, 4);
v___x_2117_ = lean_unsigned_to_nat(3u);
v___x_2118_ = lean_nat_mul(v___x_2117_, v_size_2111_);
v___x_2119_ = lean_nat_dec_lt(v___x_2118_, v_size_2112_);
lean_dec(v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_l_2115_);
v___x_2120_ = lean_nat_add(v___x_2110_, v_size_2111_);
v___x_2121_ = lean_nat_add(v___x_2120_, v_size_2112_);
lean_dec(v___x_2120_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_impl_2109_);
lean_ctor_set(v___x_1966_, 0, v___x_2121_);
v___x_2123_ = v___x_1966_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_impl_2109_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
else
{
lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2188_; 
lean_inc(v_r_2116_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_inc(v_size_2112_);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_impl_2109_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2189_ = lean_ctor_get(v_impl_2109_, 4);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_impl_2109_, 3);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_impl_2109_, 2);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_impl_2109_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_impl_2109_, 0);
lean_dec(v_unused_2193_);
v___x_2126_ = v_impl_2109_;
v_isShared_2127_ = v_isSharedCheck_2188_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v_impl_2109_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2188_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_size_2128_; lean_object* v_k_2129_; lean_object* v_v_2130_; lean_object* v_l_2131_; lean_object* v_r_2132_; lean_object* v_size_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_size_2128_ = lean_ctor_get(v_l_2115_, 0);
v_k_2129_ = lean_ctor_get(v_l_2115_, 1);
v_v_2130_ = lean_ctor_get(v_l_2115_, 2);
v_l_2131_ = lean_ctor_get(v_l_2115_, 3);
v_r_2132_ = lean_ctor_get(v_l_2115_, 4);
v_size_2133_ = lean_ctor_get(v_r_2116_, 0);
v___x_2134_ = lean_unsigned_to_nat(2u);
v___x_2135_ = lean_nat_mul(v___x_2134_, v_size_2133_);
v___x_2136_ = lean_nat_dec_lt(v_size_2128_, v___x_2135_);
lean_dec(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_r_2132_);
lean_inc(v_l_2131_);
lean_inc(v_v_2130_);
lean_inc(v_k_2129_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_l_2115_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2165_ = lean_ctor_get(v_l_2115_, 4);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_l_2115_, 3);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_l_2115_, 2);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_l_2115_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2115_, 0);
lean_dec(v_unused_2169_);
v___x_2138_ = v_l_2115_;
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
else
{
lean_dec(v_l_2115_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2154_; 
v___x_2140_ = lean_nat_add(v___x_2110_, v_size_2111_);
v___x_2141_ = lean_nat_add(v___x_2140_, v_size_2112_);
lean_dec(v_size_2112_);
if (lean_obj_tag(v_l_2131_) == 0)
{
lean_object* v_size_2162_; 
v_size_2162_ = lean_ctor_get(v_l_2131_, 0);
lean_inc(v_size_2162_);
v___y_2154_ = v_size_2162_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_unsigned_to_nat(0u);
v___y_2154_ = v___x_2163_;
goto v___jp_2153_;
}
v___jp_2142_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_nat_add(v___y_2143_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec(v___y_2143_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 4, v_r_2116_);
lean_ctor_set(v___x_2138_, 3, v_r_2132_);
lean_ctor_set(v___x_2138_, 2, v_v_2114_);
lean_ctor_set(v___x_2138_, 1, v_k_2113_);
lean_ctor_set(v___x_2138_, 0, v___x_2146_);
v___x_2148_ = v___x_2138_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_r_2132_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_r_2116_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 4, v___x_2148_);
lean_ctor_set(v___x_2126_, 3, v___y_2144_);
lean_ctor_set(v___x_2126_, 2, v_v_2130_);
lean_ctor_set(v___x_2126_, 1, v_k_2129_);
lean_ctor_set(v___x_2126_, 0, v___x_2141_);
v___x_2150_ = v___x_2126_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_k_2129_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_v_2130_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v___y_2144_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_nat_add(v___x_2140_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec(v___x_2140_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_l_2131_);
lean_ctor_set(v___x_1966_, 0, v___x_2155_);
v___x_2157_ = v___x_1966_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_l_2131_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_nat_add(v___x_2110_, v_size_2133_);
if (lean_obj_tag(v_r_2132_) == 0)
{
lean_object* v_size_2159_; 
v_size_2159_ = lean_ctor_get(v_r_2132_, 0);
lean_inc(v_size_2159_);
v___y_2143_ = v___x_2158_;
v___y_2144_ = v___x_2157_;
v___y_2145_ = v_size_2159_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_unsigned_to_nat(0u);
v___y_2143_ = v___x_2158_;
v___y_2144_ = v___x_2157_;
v___y_2145_ = v___x_2160_;
goto v___jp_2142_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_del_object(v___x_1966_);
v___x_2170_ = lean_nat_add(v___x_2110_, v_size_2111_);
v___x_2171_ = lean_nat_add(v___x_2170_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2172_ = lean_nat_add(v___x_2170_, v_size_2128_);
lean_dec(v___x_2170_);
lean_inc_ref(v_l_1963_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 4, v_l_2115_);
lean_ctor_set(v___x_2126_, 3, v_l_1963_);
lean_ctor_set(v___x_2126_, 2, v_v_1962_);
lean_ctor_set(v___x_2126_, 1, v_k_1961_);
lean_ctor_set(v___x_2126_, 0, v___x_2172_);
v___x_2174_ = v___x_2126_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_l_2115_);
v___x_2174_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_isSharedCheck_2181_ = !lean_is_exclusive(v_l_1963_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2182_ = lean_ctor_get(v_l_1963_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_1963_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_1963_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_l_1963_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_l_1963_, 0);
lean_dec(v_unused_2186_);
v___x_2176_ = v_l_1963_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v_l_1963_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 4, v_r_2116_);
lean_ctor_set(v___x_2176_, 3, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v_v_2114_);
lean_ctor_set(v___x_2176_, 1, v_k_2113_);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_r_2116_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2194_; 
v_l_2194_ = lean_ctor_get(v_impl_2109_, 3);
lean_inc(v_l_2194_);
if (lean_obj_tag(v_l_2194_) == 0)
{
lean_object* v_r_2195_; lean_object* v_k_2196_; lean_object* v_v_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2220_; 
v_r_2195_ = lean_ctor_get(v_impl_2109_, 4);
v_k_2196_ = lean_ctor_get(v_impl_2109_, 1);
v_v_2197_ = lean_ctor_get(v_impl_2109_, 2);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_impl_2109_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; 
v_unused_2221_ = lean_ctor_get(v_impl_2109_, 3);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_impl_2109_, 0);
lean_dec(v_unused_2222_);
v___x_2199_ = v_impl_2109_;
v_isShared_2200_ = v_isSharedCheck_2220_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_r_2195_);
lean_inc(v_v_2197_);
lean_inc(v_k_2196_);
lean_dec(v_impl_2109_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2220_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_k_2201_; lean_object* v_v_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2216_; 
v_k_2201_ = lean_ctor_get(v_l_2194_, 1);
v_v_2202_ = lean_ctor_get(v_l_2194_, 2);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_l_2194_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; 
v_unused_2217_ = lean_ctor_get(v_l_2194_, 4);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_l_2194_, 3);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_l_2194_, 0);
lean_dec(v_unused_2219_);
v___x_2204_ = v_l_2194_;
v_isShared_2205_ = v_isSharedCheck_2216_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_v_2202_);
lean_inc(v_k_2201_);
lean_dec(v_l_2194_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2216_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2195_, 2);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 4, v_r_2195_);
lean_ctor_set(v___x_2204_, 3, v_r_2195_);
lean_ctor_set(v___x_2204_, 2, v_v_1962_);
lean_ctor_set(v___x_2204_, 1, v_k_1961_);
lean_ctor_set(v___x_2204_, 0, v___x_2110_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_r_2195_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_r_2195_);
v___x_2208_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2210_; 
lean_inc(v_r_2195_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 3, v_r_2195_);
lean_ctor_set(v___x_2199_, 0, v___x_2110_);
v___x_2210_ = v___x_2199_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_2196_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_2197_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_r_2195_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_r_2195_);
v___x_2210_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2212_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v___x_2210_);
lean_ctor_set(v___x_1966_, 3, v___x_2208_);
lean_ctor_set(v___x_1966_, 2, v_v_2202_);
lean_ctor_set(v___x_1966_, 1, v_k_2201_);
lean_ctor_set(v___x_1966_, 0, v___x_2206_);
v___x_2212_ = v___x_1966_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_k_2201_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2202_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
else
{
lean_object* v_r_2223_; 
v_r_2223_ = lean_ctor_get(v_impl_2109_, 4);
lean_inc(v_r_2223_);
if (lean_obj_tag(v_r_2223_) == 0)
{
lean_object* v_k_2224_; lean_object* v_v_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2236_; 
v_k_2224_ = lean_ctor_get(v_impl_2109_, 1);
v_v_2225_ = lean_ctor_get(v_impl_2109_, 2);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_impl_2109_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; lean_object* v_unused_2238_; lean_object* v_unused_2239_; 
v_unused_2237_ = lean_ctor_get(v_impl_2109_, 4);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_impl_2109_, 3);
lean_dec(v_unused_2238_);
v_unused_2239_ = lean_ctor_get(v_impl_2109_, 0);
lean_dec(v_unused_2239_);
v___x_2227_ = v_impl_2109_;
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_v_2225_);
lean_inc(v_k_2224_);
lean_dec(v_impl_2109_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(3u);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 4, v_l_2194_);
lean_ctor_set(v___x_2227_, 2, v_v_1962_);
lean_ctor_set(v___x_2227_, 1, v_k_1961_);
lean_ctor_set(v___x_2227_, 0, v___x_2110_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_l_2194_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_l_2194_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_r_2223_);
lean_ctor_set(v___x_1966_, 3, v___x_2231_);
lean_ctor_set(v___x_1966_, 2, v_v_2225_);
lean_ctor_set(v___x_1966_, 1, v_k_2224_);
lean_ctor_set(v___x_1966_, 0, v___x_2229_);
v___x_2233_ = v___x_1966_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_r_2223_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_unsigned_to_nat(2u);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 4, v_impl_2109_);
lean_ctor_set(v___x_1966_, 3, v_r_2223_);
lean_ctor_set(v___x_1966_, 0, v___x_2240_);
v___x_2242_ = v___x_1966_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_k_1961_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_v_1962_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_r_2223_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_impl_2109_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
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
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v_k_1957_);
lean_ctor_set(v___x_2246_, 2, v_v_1958_);
lean_ctor_set(v___x_2246_, 3, v_t_1959_);
lean_ctor_set(v___x_2246_, 4, v_t_1959_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2247_, lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_object* v_k_2249_; lean_object* v_v_2250_; lean_object* v_l_2251_; lean_object* v_r_2252_; lean_object* v___x_2253_; 
v_k_2249_ = lean_ctor_get(v_x_2248_, 1);
lean_inc(v_k_2249_);
v_v_2250_ = lean_ctor_get(v_x_2248_, 2);
lean_inc(v_v_2250_);
v_l_2251_ = lean_ctor_get(v_x_2248_, 3);
lean_inc(v_l_2251_);
v_r_2252_ = lean_ctor_get(v_x_2248_, 4);
lean_inc(v_r_2252_);
lean_dec_ref_known(v_x_2248_, 5);
v___x_2253_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2247_, v_l_2251_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_dec(v_r_2252_);
lean_dec(v_v_2250_);
lean_dec(v_k_2249_);
return v___x_2253_;
}
else
{
if (lean_obj_tag(v_v_2250_) == 4)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2368_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2368_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2368_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_elems_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_elems_2258_ = lean_ctor_get(v_v_2250_, 0);
lean_inc_ref(v_elems_2258_);
lean_dec_ref_known(v_v_2250_, 1);
v___x_2259_ = lean_array_get_size(v_elems_2258_);
v___x_2260_ = lean_unsigned_to_nat(8u);
v___x_2261_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
v___x_2262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2263_ = l_Nat_reprFast(v___x_2259_);
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
lean_dec_ref(v___x_2263_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2264_);
v___x_2266_ = v___x_2256_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_del_object(v___x_2256_);
v___x_2268_ = lean_box(0);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2269_);
lean_inc(v___x_2270_);
v___x_2271_ = l_Lean_Json_getNat_x3f(v___x_2270_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2281_);
lean_inc(v___x_2282_);
v___x_2283_ = l_Lean_Json_getNat_x3f(v___x_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
v___x_2293_ = lean_unsigned_to_nat(2u);
v___x_2294_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2293_);
lean_inc(v___x_2294_);
v___x_2295_ = l_Lean_Json_getNat_x3f(v___x_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
v___x_2305_ = lean_unsigned_to_nat(3u);
v___x_2306_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2305_);
lean_inc(v___x_2306_);
v___x_2307_ = l_Lean_Json_getNat_x3f(v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
v___x_2317_ = lean_unsigned_to_nat(4u);
v___x_2318_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2317_);
lean_inc(v___x_2318_);
v___x_2319_ = l_Lean_Json_getNat_x3f(v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
v___x_2329_ = lean_unsigned_to_nat(5u);
v___x_2330_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2329_);
lean_inc(v___x_2330_);
v___x_2331_ = l_Lean_Json_getNat_x3f(v___x_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_a_2328_);
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
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
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2340_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2341_ = lean_unsigned_to_nat(6u);
v___x_2342_ = lean_array_get_borrowed(v___x_2268_, v_elems_2258_, v___x_2341_);
lean_inc(v___x_2342_);
v___x_2343_ = l_Lean_Json_getNat_x3f(v___x_2342_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2340_);
lean_dec(v_a_2328_);
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec_ref(v_elems_2258_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2352_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2353_ = lean_unsigned_to_nat(7u);
v___x_2354_ = lean_array_get(v___x_2268_, v_elems_2258_, v___x_2353_);
lean_dec_ref(v_elems_2258_);
v___x_2355_ = l_Lean_Json_getNat_x3f(v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_a_2352_);
lean_dec(v_a_2340_);
lean_dec(v_a_2328_);
lean_dec(v_a_2316_);
lean_dec(v_a_2304_);
lean_dec(v_a_2292_);
lean_dec(v_a_2280_);
lean_dec(v_a_2254_);
lean_dec(v_r_2252_);
lean_dec(v_k_2249_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2365_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2365_, 0, v_a_2280_);
lean_ctor_set(v___x_2365_, 1, v_a_2292_);
lean_ctor_set(v___x_2365_, 2, v_a_2304_);
lean_ctor_set(v___x_2365_, 3, v_a_2316_);
lean_ctor_set(v___x_2365_, 4, v_a_2328_);
lean_ctor_set(v___x_2365_, 5, v_a_2340_);
lean_ctor_set(v___x_2365_, 6, v_a_2352_);
lean_ctor_set(v___x_2365_, 7, v_a_2364_);
v___x_2366_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2249_, v___x_2365_, v_a_2254_);
v_init_2247_ = v___x_2366_;
v_x_2248_ = v_r_2252_;
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
lean_object* v___x_2369_; 
lean_dec_ref_known(v___x_2253_, 1);
lean_dec(v_r_2252_);
lean_dec(v_v_2250_);
lean_dec(v_k_2249_);
v___x_2369_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__0___closed__0));
return v___x_2369_;
}
}
}
else
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2370_, 0, v_init_2247_);
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2371_, lean_object* v_k_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = l_Lean_Json_getObjValD(v_j_2371_, v_k_2372_);
v___x_2374_ = l_Lean_Json_getObj_x3f(v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_a_2383_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2384_ = lean_box(1);
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2384_, v_a_2383_);
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2386_, lean_object* v_k_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2386_, v_k_2387_);
lean_dec_ref(v_k_2387_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2389_, size_t v_i_2390_, lean_object* v_bs_2391_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = lean_usize_dec_lt(v_i_2390_, v_sz_2389_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_bs_2391_);
return v___x_2393_;
}
else
{
lean_object* v_v_2394_; lean_object* v___x_2395_; lean_object* v_bs_x27_2396_; size_t v___x_2397_; size_t v___x_2398_; lean_object* v___x_2399_; 
v_v_2394_ = lean_array_uget(v_bs_2391_, v_i_2390_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v_bs_x27_2396_ = lean_array_uset(v_bs_2391_, v_i_2390_, v___x_2395_);
v___x_2397_ = ((size_t)1ULL);
v___x_2398_ = lean_usize_add(v_i_2390_, v___x_2397_);
v___x_2399_ = lean_array_uset(v_bs_x27_2396_, v_i_2390_, v_v_2394_);
v_i_2390_ = v___x_2398_;
v_bs_2391_ = v___x_2399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_bs_2403_){
_start:
{
size_t v_sz_boxed_2404_; size_t v_i_boxed_2405_; lean_object* v_res_2406_; 
v_sz_boxed_2404_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2405_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2404_, v_i_boxed_2405_, v_bs_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 4)
{
lean_object* v_elems_2408_; size_t v_sz_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
v_elems_2408_ = lean_ctor_get(v_x_2407_, 0);
lean_inc_ref(v_elems_2408_);
lean_dec_ref_known(v_x_2407_, 1);
v_sz_2409_ = lean_array_size(v_elems_2408_);
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2409_, v___x_2410_, v_elems_2408_);
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2412_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2413_ = lean_unsigned_to_nat(80u);
v___x_2414_ = l_Lean_Json_pretty(v_x_2407_, v___x_2413_);
v___x_2415_ = lean_string_append(v___x_2412_, v___x_2414_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2417_ = lean_string_append(v___x_2415_, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_a_2432_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___x_2423_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2423_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2441_, lean_object* v_k_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = l_Lean_Json_getObjValD(v_j_2441_, v_k_2442_);
v___x_2444_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2445_, v_k_2446_);
lean_dec_ref(v_k_2446_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2448_, lean_object* v_v_2449_, lean_object* v_t_2450_){
_start:
{
if (lean_obj_tag(v_t_2450_) == 0)
{
lean_object* v_size_2451_; lean_object* v_k_2452_; lean_object* v_v_2453_; lean_object* v_l_2454_; lean_object* v_r_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2735_; 
v_size_2451_ = lean_ctor_get(v_t_2450_, 0);
v_k_2452_ = lean_ctor_get(v_t_2450_, 1);
v_v_2453_ = lean_ctor_get(v_t_2450_, 2);
v_l_2454_ = lean_ctor_get(v_t_2450_, 3);
v_r_2455_ = lean_ctor_get(v_t_2450_, 4);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_t_2450_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2457_ = v_t_2450_;
v_isShared_2458_ = v_isSharedCheck_2735_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_r_2455_);
lean_inc(v_l_2454_);
lean_inc(v_v_2453_);
lean_inc(v_k_2452_);
lean_inc(v_size_2451_);
lean_dec(v_t_2450_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2735_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
uint8_t v___x_2459_; 
v___x_2459_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2448_, v_k_2452_);
switch(v___x_2459_)
{
case 0:
{
lean_object* v_impl_2460_; lean_object* v___x_2461_; 
lean_dec(v_size_2451_);
v_impl_2460_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2448_, v_v_2449_, v_l_2454_);
v___x_2461_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2455_) == 0)
{
lean_object* v_size_2462_; lean_object* v_size_2463_; lean_object* v_k_2464_; lean_object* v_v_2465_; lean_object* v_l_2466_; lean_object* v_r_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_size_2462_ = lean_ctor_get(v_r_2455_, 0);
v_size_2463_ = lean_ctor_get(v_impl_2460_, 0);
v_k_2464_ = lean_ctor_get(v_impl_2460_, 1);
v_v_2465_ = lean_ctor_get(v_impl_2460_, 2);
v_l_2466_ = lean_ctor_get(v_impl_2460_, 3);
v_r_2467_ = lean_ctor_get(v_impl_2460_, 4);
lean_inc(v_r_2467_);
v___x_2468_ = lean_unsigned_to_nat(3u);
v___x_2469_ = lean_nat_mul(v___x_2468_, v_size_2462_);
v___x_2470_ = lean_nat_dec_lt(v___x_2469_, v_size_2463_);
lean_dec(v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_r_2467_);
v___x_2471_ = lean_nat_add(v___x_2461_, v_size_2463_);
v___x_2472_ = lean_nat_add(v___x_2471_, v_size_2462_);
lean_dec(v___x_2471_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 3, v_impl_2460_);
lean_ctor_set(v___x_2457_, 0, v___x_2472_);
v___x_2474_ = v___x_2457_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_impl_2460_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_r_2455_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
else
{
lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2541_; 
lean_inc(v_l_2466_);
lean_inc(v_v_2465_);
lean_inc(v_k_2464_);
lean_inc(v_size_2463_);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; lean_object* v_unused_2543_; lean_object* v_unused_2544_; lean_object* v_unused_2545_; lean_object* v_unused_2546_; 
v_unused_2542_ = lean_ctor_get(v_impl_2460_, 4);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2543_);
v_unused_2544_ = lean_ctor_get(v_impl_2460_, 2);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_impl_2460_, 1);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2546_);
v___x_2477_ = v_impl_2460_;
v_isShared_2478_ = v_isSharedCheck_2541_;
goto v_resetjp_2476_;
}
else
{
lean_dec(v_impl_2460_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2541_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_size_2479_; lean_object* v_size_2480_; lean_object* v_k_2481_; lean_object* v_v_2482_; lean_object* v_l_2483_; lean_object* v_r_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_size_2479_ = lean_ctor_get(v_l_2466_, 0);
v_size_2480_ = lean_ctor_get(v_r_2467_, 0);
v_k_2481_ = lean_ctor_get(v_r_2467_, 1);
v_v_2482_ = lean_ctor_get(v_r_2467_, 2);
v_l_2483_ = lean_ctor_get(v_r_2467_, 3);
v_r_2484_ = lean_ctor_get(v_r_2467_, 4);
v___x_2485_ = lean_unsigned_to_nat(2u);
v___x_2486_ = lean_nat_mul(v___x_2485_, v_size_2479_);
v___x_2487_ = lean_nat_dec_lt(v_size_2480_, v___x_2486_);
lean_dec(v___x_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2516_; 
lean_inc(v_r_2484_);
lean_inc(v_l_2483_);
lean_inc(v_v_2482_);
lean_inc(v_k_2481_);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_r_2467_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2517_ = lean_ctor_get(v_r_2467_, 4);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_r_2467_, 3);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_r_2467_, 2);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_r_2467_, 1);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_r_2467_, 0);
lean_dec(v_unused_2521_);
v___x_2489_ = v_r_2467_;
v_isShared_2490_ = v_isSharedCheck_2516_;
goto v_resetjp_2488_;
}
else
{
lean_dec(v_r_2467_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2516_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___x_2504_; lean_object* v___y_2506_; 
v___x_2491_ = lean_nat_add(v___x_2461_, v_size_2463_);
lean_dec(v_size_2463_);
v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2462_);
lean_dec(v___x_2491_);
v___x_2504_ = lean_nat_add(v___x_2461_, v_size_2479_);
if (lean_obj_tag(v_l_2483_) == 0)
{
lean_object* v_size_2514_; 
v_size_2514_ = lean_ctor_get(v_l_2483_, 0);
lean_inc(v_size_2514_);
v___y_2506_ = v_size_2514_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___y_2506_ = v___x_2515_;
goto v___jp_2505_;
}
v___jp_2493_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = lean_nat_add(v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec(v___y_2495_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 4, v_r_2455_);
lean_ctor_set(v___x_2489_, 3, v_r_2484_);
lean_ctor_set(v___x_2489_, 2, v_v_2453_);
lean_ctor_set(v___x_2489_, 1, v_k_2452_);
lean_ctor_set(v___x_2489_, 0, v___x_2497_);
v___x_2499_ = v___x_2489_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_r_2484_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_r_2455_);
v___x_2499_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v___x_2499_);
lean_ctor_set(v___x_2477_, 3, v___y_2494_);
lean_ctor_set(v___x_2477_, 2, v_v_2482_);
lean_ctor_set(v___x_2477_, 1, v_k_2481_);
lean_ctor_set(v___x_2477_, 0, v___x_2492_);
v___x_2501_ = v___x_2477_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2481_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2482_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___y_2494_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_nat_add(v___x_2504_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec(v___x_2504_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_l_2483_);
lean_ctor_set(v___x_2457_, 3, v_l_2466_);
lean_ctor_set(v___x_2457_, 2, v_v_2465_);
lean_ctor_set(v___x_2457_, 1, v_k_2464_);
lean_ctor_set(v___x_2457_, 0, v___x_2507_);
v___x_2509_ = v___x_2457_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_l_2466_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_l_2483_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_nat_add(v___x_2461_, v_size_2462_);
if (lean_obj_tag(v_r_2484_) == 0)
{
lean_object* v_size_2511_; 
v_size_2511_ = lean_ctor_get(v_r_2484_, 0);
lean_inc(v_size_2511_);
v___y_2494_ = v___x_2509_;
v___y_2495_ = v___x_2510_;
v___y_2496_ = v_size_2511_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_unsigned_to_nat(0u);
v___y_2494_ = v___x_2509_;
v___y_2495_ = v___x_2510_;
v___y_2496_ = v___x_2512_;
goto v___jp_2493_;
}
}
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
lean_del_object(v___x_2457_);
v___x_2522_ = lean_nat_add(v___x_2461_, v_size_2463_);
lean_dec(v_size_2463_);
v___x_2523_ = lean_nat_add(v___x_2522_, v_size_2462_);
lean_dec(v___x_2522_);
v___x_2524_ = lean_nat_add(v___x_2461_, v_size_2462_);
v___x_2525_ = lean_nat_add(v___x_2524_, v_size_2480_);
lean_dec(v___x_2524_);
lean_inc_ref(v_r_2455_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v_r_2455_);
lean_ctor_set(v___x_2477_, 3, v_r_2467_);
lean_ctor_set(v___x_2477_, 2, v_v_2453_);
lean_ctor_set(v___x_2477_, 1, v_k_2452_);
lean_ctor_set(v___x_2477_, 0, v___x_2525_);
v___x_2527_ = v___x_2477_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_r_2467_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_r_2455_);
v___x_2527_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_isSharedCheck_2534_ = !lean_is_exclusive(v_r_2455_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; 
v_unused_2535_ = lean_ctor_get(v_r_2455_, 4);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_r_2455_, 3);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_r_2455_, 2);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_r_2455_, 1);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_r_2455_, 0);
lean_dec(v_unused_2539_);
v___x_2529_ = v_r_2455_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v_r_2455_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 4, v___x_2527_);
lean_ctor_set(v___x_2529_, 3, v_l_2466_);
lean_ctor_set(v___x_2529_, 2, v_v_2465_);
lean_ctor_set(v___x_2529_, 1, v_k_2464_);
lean_ctor_set(v___x_2529_, 0, v___x_2523_);
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_l_2466_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___x_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2547_; 
v_l_2547_ = lean_ctor_get(v_impl_2460_, 3);
if (lean_obj_tag(v_l_2547_) == 0)
{
lean_object* v_r_2548_; lean_object* v_k_2549_; lean_object* v_v_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2561_; 
lean_inc_ref(v_l_2547_);
v_r_2548_ = lean_ctor_get(v_impl_2460_, 4);
v_k_2549_ = lean_ctor_get(v_impl_2460_, 1);
v_v_2550_ = lean_ctor_get(v_impl_2460_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; lean_object* v_unused_2563_; 
v_unused_2562_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2563_);
v___x_2552_ = v_impl_2460_;
v_isShared_2553_ = v_isSharedCheck_2561_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_r_2548_);
lean_inc(v_v_2550_);
lean_inc(v_k_2549_);
lean_dec(v_impl_2460_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2561_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2548_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 3, v_r_2548_);
lean_ctor_set(v___x_2552_, 2, v_v_2453_);
lean_ctor_set(v___x_2552_, 1, v_k_2452_);
lean_ctor_set(v___x_2552_, 0, v___x_2461_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_r_2548_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v_r_2548_);
v___x_2556_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2558_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v___x_2556_);
lean_ctor_set(v___x_2457_, 3, v_l_2547_);
lean_ctor_set(v___x_2457_, 2, v_v_2550_);
lean_ctor_set(v___x_2457_, 1, v_k_2549_);
lean_ctor_set(v___x_2457_, 0, v___x_2554_);
v___x_2558_ = v___x_2457_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_l_2547_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v_r_2564_; 
v_r_2564_ = lean_ctor_get(v_impl_2460_, 4);
lean_inc(v_r_2564_);
if (lean_obj_tag(v_r_2564_) == 0)
{
lean_object* v_k_2565_; lean_object* v_v_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2589_; 
lean_inc(v_l_2547_);
v_k_2565_ = lean_ctor_get(v_impl_2460_, 1);
v_v_2566_ = lean_ctor_get(v_impl_2460_, 2);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_impl_2460_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; lean_object* v_unused_2591_; lean_object* v_unused_2592_; 
v_unused_2590_ = lean_ctor_get(v_impl_2460_, 4);
lean_dec(v_unused_2590_);
v_unused_2591_ = lean_ctor_get(v_impl_2460_, 3);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_impl_2460_, 0);
lean_dec(v_unused_2592_);
v___x_2568_ = v_impl_2460_;
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_v_2566_);
lean_inc(v_k_2565_);
lean_dec(v_impl_2460_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2585_; 
v_k_2570_ = lean_ctor_get(v_r_2564_, 1);
v_v_2571_ = lean_ctor_get(v_r_2564_, 2);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_r_2564_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2586_ = lean_ctor_get(v_r_2564_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v_r_2564_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_r_2564_, 0);
lean_dec(v_unused_2588_);
v___x_2573_ = v_r_2564_;
v_isShared_2574_ = v_isSharedCheck_2585_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_v_2571_);
lean_inc(v_k_2570_);
lean_dec(v_r_2564_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2585_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_unsigned_to_nat(3u);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 4, v_l_2547_);
lean_ctor_set(v___x_2573_, 3, v_l_2547_);
lean_ctor_set(v___x_2573_, 2, v_v_2566_);
lean_ctor_set(v___x_2573_, 1, v_k_2565_);
lean_ctor_set(v___x_2573_, 0, v___x_2461_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_2565_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_2566_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_l_2547_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_l_2547_);
v___x_2577_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 4, v_l_2547_);
lean_ctor_set(v___x_2568_, 2, v_v_2453_);
lean_ctor_set(v___x_2568_, 1, v_k_2452_);
lean_ctor_set(v___x_2568_, 0, v___x_2461_);
v___x_2579_ = v___x_2568_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_l_2547_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_l_2547_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v___x_2579_);
lean_ctor_set(v___x_2457_, 3, v___x_2577_);
lean_ctor_set(v___x_2457_, 2, v_v_2571_);
lean_ctor_set(v___x_2457_, 1, v_k_2570_);
lean_ctor_set(v___x_2457_, 0, v___x_2575_);
v___x_2581_ = v___x_2457_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = lean_unsigned_to_nat(2u);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2564_);
lean_ctor_set(v___x_2457_, 3, v_impl_2460_);
lean_ctor_set(v___x_2457_, 0, v___x_2593_);
v___x_2595_ = v___x_2457_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_impl_2460_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_r_2564_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2598_; 
lean_dec(v_v_2453_);
lean_dec(v_k_2452_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 2, v_v_2449_);
lean_ctor_set(v___x_2457_, 1, v_k_2448_);
v___x_2598_ = v___x_2457_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_size_2451_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_k_2448_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v_v_2449_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v_l_2454_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v_r_2455_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
default: 
{
lean_object* v_impl_2600_; lean_object* v___x_2601_; 
lean_dec(v_size_2451_);
v_impl_2600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2448_, v_v_2449_, v_r_2455_);
v___x_2601_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2454_) == 0)
{
lean_object* v_size_2602_; lean_object* v_size_2603_; lean_object* v_k_2604_; lean_object* v_v_2605_; lean_object* v_l_2606_; lean_object* v_r_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_size_2602_ = lean_ctor_get(v_l_2454_, 0);
v_size_2603_ = lean_ctor_get(v_impl_2600_, 0);
v_k_2604_ = lean_ctor_get(v_impl_2600_, 1);
v_v_2605_ = lean_ctor_get(v_impl_2600_, 2);
v_l_2606_ = lean_ctor_get(v_impl_2600_, 3);
lean_inc(v_l_2606_);
v_r_2607_ = lean_ctor_get(v_impl_2600_, 4);
v___x_2608_ = lean_unsigned_to_nat(3u);
v___x_2609_ = lean_nat_mul(v___x_2608_, v_size_2602_);
v___x_2610_ = lean_nat_dec_lt(v___x_2609_, v_size_2603_);
lean_dec(v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec(v_l_2606_);
v___x_2611_ = lean_nat_add(v___x_2601_, v_size_2602_);
v___x_2612_ = lean_nat_add(v___x_2611_, v_size_2603_);
lean_dec(v___x_2611_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_impl_2600_);
lean_ctor_set(v___x_2457_, 0, v___x_2612_);
v___x_2614_ = v___x_2457_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_l_2454_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_impl_2600_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
else
{
lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2679_; 
lean_inc(v_r_2607_);
lean_inc(v_v_2605_);
lean_inc(v_k_2604_);
lean_inc(v_size_2603_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_impl_2600_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; lean_object* v_unused_2683_; lean_object* v_unused_2684_; 
v_unused_2680_ = lean_ctor_get(v_impl_2600_, 4);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_impl_2600_, 3);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_impl_2600_, 2);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_impl_2600_, 1);
lean_dec(v_unused_2683_);
v_unused_2684_ = lean_ctor_get(v_impl_2600_, 0);
lean_dec(v_unused_2684_);
v___x_2617_ = v_impl_2600_;
v_isShared_2618_ = v_isSharedCheck_2679_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v_impl_2600_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2679_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_size_2619_; lean_object* v_k_2620_; lean_object* v_v_2621_; lean_object* v_l_2622_; lean_object* v_r_2623_; lean_object* v_size_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_size_2619_ = lean_ctor_get(v_l_2606_, 0);
v_k_2620_ = lean_ctor_get(v_l_2606_, 1);
v_v_2621_ = lean_ctor_get(v_l_2606_, 2);
v_l_2622_ = lean_ctor_get(v_l_2606_, 3);
v_r_2623_ = lean_ctor_get(v_l_2606_, 4);
v_size_2624_ = lean_ctor_get(v_r_2607_, 0);
v___x_2625_ = lean_unsigned_to_nat(2u);
v___x_2626_ = lean_nat_mul(v___x_2625_, v_size_2624_);
v___x_2627_ = lean_nat_dec_lt(v_size_2619_, v___x_2626_);
lean_dec(v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2655_; 
lean_inc(v_r_2623_);
lean_inc(v_l_2622_);
lean_inc(v_v_2621_);
lean_inc(v_k_2620_);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_l_2606_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; 
v_unused_2656_ = lean_ctor_get(v_l_2606_, 4);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_l_2606_, 3);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_l_2606_, 2);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_l_2606_, 1);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_l_2606_, 0);
lean_dec(v_unused_2660_);
v___x_2629_ = v_l_2606_;
v_isShared_2630_ = v_isSharedCheck_2655_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v_l_2606_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2655_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2645_; 
v___x_2631_ = lean_nat_add(v___x_2601_, v_size_2602_);
v___x_2632_ = lean_nat_add(v___x_2631_, v_size_2603_);
lean_dec(v_size_2603_);
if (lean_obj_tag(v_l_2622_) == 0)
{
lean_object* v_size_2653_; 
v_size_2653_ = lean_ctor_get(v_l_2622_, 0);
lean_inc(v_size_2653_);
v___y_2645_ = v_size_2653_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___y_2645_ = v___x_2654_;
goto v___jp_2644_;
}
v___jp_2633_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_nat_add(v___y_2634_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec(v___y_2634_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 4, v_r_2607_);
lean_ctor_set(v___x_2629_, 3, v_r_2623_);
lean_ctor_set(v___x_2629_, 2, v_v_2605_);
lean_ctor_set(v___x_2629_, 1, v_k_2604_);
lean_ctor_set(v___x_2629_, 0, v___x_2637_);
v___x_2639_ = v___x_2629_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2604_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2605_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_r_2623_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_r_2607_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___x_2639_);
lean_ctor_set(v___x_2617_, 3, v___y_2635_);
lean_ctor_set(v___x_2617_, 2, v_v_2621_);
lean_ctor_set(v___x_2617_, 1, v_k_2620_);
lean_ctor_set(v___x_2617_, 0, v___x_2632_);
v___x_2641_ = v___x_2617_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_k_2620_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_v_2621_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v___y_2635_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = lean_nat_add(v___x_2631_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec(v___x_2631_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_l_2622_);
lean_ctor_set(v___x_2457_, 0, v___x_2646_);
v___x_2648_ = v___x_2457_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_l_2454_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_l_2622_);
v___x_2648_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_nat_add(v___x_2601_, v_size_2624_);
if (lean_obj_tag(v_r_2623_) == 0)
{
lean_object* v_size_2650_; 
v_size_2650_ = lean_ctor_get(v_r_2623_, 0);
lean_inc(v_size_2650_);
v___y_2634_ = v___x_2649_;
v___y_2635_ = v___x_2648_;
v___y_2636_ = v_size_2650_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___y_2634_ = v___x_2649_;
v___y_2635_ = v___x_2648_;
v___y_2636_ = v___x_2651_;
goto v___jp_2633_;
}
}
}
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
lean_del_object(v___x_2457_);
v___x_2661_ = lean_nat_add(v___x_2601_, v_size_2602_);
v___x_2662_ = lean_nat_add(v___x_2661_, v_size_2603_);
lean_dec(v_size_2603_);
v___x_2663_ = lean_nat_add(v___x_2661_, v_size_2619_);
lean_dec(v___x_2661_);
lean_inc_ref(v_l_2454_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v_l_2606_);
lean_ctor_set(v___x_2617_, 3, v_l_2454_);
lean_ctor_set(v___x_2617_, 2, v_v_2453_);
lean_ctor_set(v___x_2617_, 1, v_k_2452_);
lean_ctor_set(v___x_2617_, 0, v___x_2663_);
v___x_2665_ = v___x_2617_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_l_2454_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v_l_2606_);
v___x_2665_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_isSharedCheck_2672_ = !lean_is_exclusive(v_l_2454_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; 
v_unused_2673_ = lean_ctor_get(v_l_2454_, 4);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_l_2454_, 3);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_l_2454_, 2);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2454_, 1);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2454_, 0);
lean_dec(v_unused_2677_);
v___x_2667_ = v_l_2454_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v_l_2454_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 4, v_r_2607_);
lean_ctor_set(v___x_2667_, 3, v___x_2665_);
lean_ctor_set(v___x_2667_, 2, v_v_2605_);
lean_ctor_set(v___x_2667_, 1, v_k_2604_);
lean_ctor_set(v___x_2667_, 0, v___x_2662_);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2604_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2605_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_r_2607_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2685_; 
v_l_2685_ = lean_ctor_get(v_impl_2600_, 3);
lean_inc(v_l_2685_);
if (lean_obj_tag(v_l_2685_) == 0)
{
lean_object* v_r_2686_; lean_object* v_k_2687_; lean_object* v_v_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2711_; 
v_r_2686_ = lean_ctor_get(v_impl_2600_, 4);
v_k_2687_ = lean_ctor_get(v_impl_2600_, 1);
v_v_2688_ = lean_ctor_get(v_impl_2600_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_impl_2600_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2712_ = lean_ctor_get(v_impl_2600_, 3);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_impl_2600_, 0);
lean_dec(v_unused_2713_);
v___x_2690_ = v_impl_2600_;
v_isShared_2691_ = v_isSharedCheck_2711_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_r_2686_);
lean_inc(v_v_2688_);
lean_inc(v_k_2687_);
lean_dec(v_impl_2600_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2711_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_k_2692_; lean_object* v_v_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2707_; 
v_k_2692_ = lean_ctor_get(v_l_2685_, 1);
v_v_2693_ = lean_ctor_get(v_l_2685_, 2);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_l_2685_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; lean_object* v_unused_2709_; lean_object* v_unused_2710_; 
v_unused_2708_ = lean_ctor_get(v_l_2685_, 4);
lean_dec(v_unused_2708_);
v_unused_2709_ = lean_ctor_get(v_l_2685_, 3);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_l_2685_, 0);
lean_dec(v_unused_2710_);
v___x_2695_ = v_l_2685_;
v_isShared_2696_ = v_isSharedCheck_2707_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_v_2693_);
lean_inc(v_k_2692_);
lean_dec(v_l_2685_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2707_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2686_, 2);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 4, v_r_2686_);
lean_ctor_set(v___x_2695_, 3, v_r_2686_);
lean_ctor_set(v___x_2695_, 2, v_v_2453_);
lean_ctor_set(v___x_2695_, 1, v_k_2452_);
lean_ctor_set(v___x_2695_, 0, v___x_2601_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_r_2686_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_r_2686_);
v___x_2699_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
lean_inc(v_r_2686_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 3, v_r_2686_);
lean_ctor_set(v___x_2690_, 0, v___x_2601_);
v___x_2701_ = v___x_2690_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_k_2687_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_v_2688_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_r_2686_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_r_2686_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v___x_2701_);
lean_ctor_set(v___x_2457_, 3, v___x_2699_);
lean_ctor_set(v___x_2457_, 2, v_v_2693_);
lean_ctor_set(v___x_2457_, 1, v_k_2692_);
lean_ctor_set(v___x_2457_, 0, v___x_2697_);
v___x_2703_ = v___x_2457_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_k_2692_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_v_2693_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
else
{
lean_object* v_r_2714_; 
v_r_2714_ = lean_ctor_get(v_impl_2600_, 4);
lean_inc(v_r_2714_);
if (lean_obj_tag(v_r_2714_) == 0)
{
lean_object* v_k_2715_; lean_object* v_v_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2727_; 
v_k_2715_ = lean_ctor_get(v_impl_2600_, 1);
v_v_2716_ = lean_ctor_get(v_impl_2600_, 2);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_impl_2600_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; 
v_unused_2728_ = lean_ctor_get(v_impl_2600_, 4);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_impl_2600_, 3);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_impl_2600_, 0);
lean_dec(v_unused_2730_);
v___x_2718_ = v_impl_2600_;
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_v_2716_);
lean_inc(v_k_2715_);
lean_dec(v_impl_2600_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_unsigned_to_nat(3u);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 4, v_l_2685_);
lean_ctor_set(v___x_2718_, 2, v_v_2453_);
lean_ctor_set(v___x_2718_, 1, v_k_2452_);
lean_ctor_set(v___x_2718_, 0, v___x_2601_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_l_2685_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_l_2685_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_r_2714_);
lean_ctor_set(v___x_2457_, 3, v___x_2722_);
lean_ctor_set(v___x_2457_, 2, v_v_2716_);
lean_ctor_set(v___x_2457_, 1, v_k_2715_);
lean_ctor_set(v___x_2457_, 0, v___x_2720_);
v___x_2724_ = v___x_2457_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2715_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2716_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_r_2714_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_unsigned_to_nat(2u);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 4, v_impl_2600_);
lean_ctor_set(v___x_2457_, 3, v_r_2714_);
lean_ctor_set(v___x_2457_, 0, v___x_2731_);
v___x_2733_ = v___x_2457_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_k_2452_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_v_2453_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_r_2714_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_impl_2600_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
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
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_k_2448_);
lean_ctor_set(v___x_2737_, 2, v_v_2449_);
lean_ctor_set(v___x_2737_, 3, v_t_2450_);
lean_ctor_set(v___x_2737_, 4, v_t_2450_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2738_, size_t v_i_2739_, lean_object* v_bs_2740_){
_start:
{
uint8_t v___x_2741_; 
v___x_2741_ = lean_usize_dec_lt(v_i_2739_, v_sz_2738_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_bs_2740_);
return v___x_2742_;
}
else
{
lean_object* v_v_2743_; lean_object* v___x_2744_; lean_object* v_bs_x27_2745_; lean_object* v_a_2747_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2818_; 
v_v_2743_ = lean_array_uget(v_bs_2740_, v_i_2739_);
v___x_2744_ = lean_unsigned_to_nat(0u);
v_bs_x27_2745_ = lean_array_uset(v_bs_2740_, v_i_2739_, v___x_2744_);
v___x_2752_ = lean_array_get_size(v_v_2743_);
v___x_2753_ = lean_unsigned_to_nat(4u);
v___x_2818_ = lean_nat_dec_eq(v___x_2752_, v___x_2753_);
if (v___x_2818_ == 0)
{
if (v___x_2741_ == 0)
{
goto v___jp_2754_;
}
else
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_unsigned_to_nat(5u);
v___x_2820_ = lean_nat_dec_eq(v___x_2752_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec_ref(v_bs_x27_2745_);
lean_dec(v_v_2743_);
v___x_2821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2822_ = l_Nat_reprFast(v___x_2752_);
v___x_2823_ = lean_string_append(v___x_2821_, v___x_2822_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
else
{
goto v___jp_2754_;
}
}
}
else
{
goto v___jp_2754_;
}
v___jp_2746_:
{
size_t v___x_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_add(v_i_2739_, v___x_2748_);
v___x_2750_ = lean_array_uset(v_bs_x27_2745_, v_i_2739_, v_a_2747_);
v_i_2739_ = v___x_2749_;
v_bs_2740_ = v___x_2750_;
goto _start;
}
v___jp_2754_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_array_fget_borrowed(v_v_2743_, v___x_2744_);
lean_inc(v___x_2755_);
v___x_2756_ = l_Lean_Json_getNat_x3f(v___x_2755_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_bs_x27_2745_);
lean_dec(v_v_2743_);
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
v___x_2766_ = lean_unsigned_to_nat(1u);
v___x_2767_ = lean_array_fget_borrowed(v_v_2743_, v___x_2766_);
lean_inc(v___x_2767_);
v___x_2768_ = l_Lean_Json_getNat_x3f(v___x_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2765_);
lean_dec_ref(v_bs_x27_2745_);
lean_dec(v_v_2743_);
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
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2777_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2778_ = lean_unsigned_to_nat(2u);
v___x_2779_ = lean_array_fget_borrowed(v_v_2743_, v___x_2778_);
lean_inc(v___x_2779_);
v___x_2780_ = l_Lean_Json_getNat_x3f(v___x_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2777_);
lean_dec(v_a_2765_);
lean_dec_ref(v_bs_x27_2745_);
lean_dec(v_v_2743_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2790_ = lean_unsigned_to_nat(3u);
v___x_2791_ = lean_array_fget_borrowed(v_v_2743_, v___x_2790_);
lean_inc(v___x_2791_);
v___x_2792_ = l_Lean_Json_getNat_x3f(v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2789_);
lean_dec(v_a_2777_);
lean_dec(v_a_2765_);
lean_dec_ref(v_bs_x27_2745_);
lean_dec(v_v_2743_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_a_2801_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2802_ = lean_unsigned_to_nat(5u);
v___x_2803_ = lean_nat_dec_eq(v___x_2752_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec(v_v_2743_);
v___x_2804_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2765_);
lean_ctor_set(v___x_2805_, 1, v_a_2777_);
lean_ctor_set(v___x_2805_, 2, v_a_2789_);
lean_ctor_set(v___x_2805_, 3, v_a_2801_);
lean_ctor_set(v___x_2805_, 4, v___x_2804_);
v_a_2747_ = v___x_2805_;
goto v___jp_2746_;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_array_fget(v_v_2743_, v___x_2753_);
lean_dec(v_v_2743_);
v___x_2807_ = l_Lean_Json_getStr_x3f(v___x_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_a_2801_);
lean_dec(v_a_2789_);
lean_dec(v_a_2777_);
lean_dec(v_a_2765_);
lean_dec_ref(v_bs_x27_2745_);
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2765_);
lean_ctor_set(v___x_2817_, 1, v_a_2777_);
lean_ctor_set(v___x_2817_, 2, v_a_2789_);
lean_ctor_set(v___x_2817_, 3, v_a_2801_);
lean_ctor_set(v___x_2817_, 4, v_a_2816_);
v_a_2747_ = v___x_2817_;
goto v___jp_2746_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2825_, lean_object* v_i_2826_, lean_object* v_bs_2827_){
_start:
{
size_t v_sz_boxed_2828_; size_t v_i_boxed_2829_; lean_object* v_res_2830_; 
v_sz_boxed_2828_ = lean_unbox_usize(v_sz_2825_);
lean_dec(v_sz_2825_);
v_i_boxed_2829_ = lean_unbox_usize(v_i_2826_);
lean_dec(v_i_2826_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2828_, v_i_boxed_2829_, v_bs_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2831_, size_t v_i_2832_, lean_object* v_bs_2833_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2832_, v_sz_2831_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_bs_2833_);
return v___x_2835_;
}
else
{
lean_object* v_v_2836_; lean_object* v___x_2837_; 
v_v_2836_ = lean_array_uget_borrowed(v_bs_2833_, v_i_2832_);
lean_inc(v_v_2836_);
v___x_2837_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2836_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec_ref(v_bs_2833_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2847_; lean_object* v_bs_x27_2848_; size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v_a_2846_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2847_ = lean_unsigned_to_nat(0u);
v_bs_x27_2848_ = lean_array_uset(v_bs_2833_, v_i_2832_, v___x_2847_);
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_add(v_i_2832_, v___x_2849_);
v___x_2851_ = lean_array_uset(v_bs_x27_2848_, v_i_2832_, v_a_2846_);
v_i_2832_ = v___x_2850_;
v_bs_2833_ = v___x_2851_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_bs_2855_){
_start:
{
size_t v_sz_boxed_2856_; size_t v_i_boxed_2857_; lean_object* v_res_2858_; 
v_sz_boxed_2856_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2857_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2856_, v_i_boxed_2857_, v_bs_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 4)
{
lean_object* v_elems_2860_; size_t v_sz_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v_elems_2860_ = lean_ctor_get(v_x_2859_, 0);
lean_inc_ref(v_elems_2860_);
lean_dec_ref_known(v_x_2859_, 1);
v_sz_2861_ = lean_array_size(v_elems_2860_);
v___x_2862_ = ((size_t)0ULL);
v___x_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2861_, v___x_2862_, v_elems_2860_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2864_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2865_ = lean_unsigned_to_nat(80u);
v___x_2866_ = l_Lean_Json_pretty(v_x_2859_, v___x_2865_);
v___x_2867_ = lean_string_append(v___x_2864_, v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2871_, lean_object* v_k_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = l_Lean_Json_getObjValD(v_j_2871_, v_k_2872_);
v___x_2874_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2875_, lean_object* v_k_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2875_, v_k_2876_);
lean_dec_ref(v_k_2876_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2878_, lean_object* v_x_2879_){
_start:
{
if (lean_obj_tag(v_x_2879_) == 0)
{
lean_object* v_k_2880_; lean_object* v_v_2881_; lean_object* v_l_2882_; lean_object* v_r_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_3043_; 
v_k_2880_ = lean_ctor_get(v_x_2879_, 1);
v_v_2881_ = lean_ctor_get(v_x_2879_, 2);
v_l_2882_ = lean_ctor_get(v_x_2879_, 3);
v_r_2883_ = lean_ctor_get(v_x_2879_, 4);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_x_2879_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v_x_2879_, 0);
lean_dec(v_unused_3044_);
v___x_2885_ = v_x_2879_;
v_isShared_2886_ = v_isSharedCheck_3043_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_r_2883_);
lean_inc(v_l_2882_);
lean_inc(v_v_2881_);
lean_inc(v_k_2880_);
lean_dec(v_x_2879_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_3043_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2878_, v_l_2882_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
lean_dec(v_k_2880_);
return v___x_2887_;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_3042_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_3042_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_3042_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Json_parse(v_k_2880_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2902_; 
v_a_2901_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2902_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v_definition_x3f_2913_; lean_object* v_a_2941_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2911_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2902_, 1);
v___x_2945_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2881_);
v___x_2946_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2881_, v___x_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3041_; 
v_a_2955_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2957_ = v___x_2946_;
v_isShared_2958_ = v_isSharedCheck_3041_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3041_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
if (lean_obj_tag(v_a_2955_) == 0)
{
lean_object* v___x_2959_; 
lean_del_object(v___x_2957_);
lean_del_object(v___x_2890_);
lean_del_object(v___x_2885_);
v___x_2959_ = lean_box(0);
v_definition_x3f_2913_ = v___x_2959_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_3032_; 
v_val_2960_ = lean_ctor_get(v_a_2955_, 0);
lean_inc(v_val_2960_);
lean_dec_ref_known(v_a_2955_, 1);
v___x_2961_ = lean_array_get_size(v_val_2960_);
v___x_2962_ = lean_unsigned_to_nat(4u);
v___x_3032_ = lean_nat_dec_eq(v___x_2961_, v___x_2962_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_unsigned_to_nat(5u);
v___x_3034_ = lean_nat_dec_eq(v___x_2961_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_val_2960_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v___x_3035_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3036_ = l_Nat_reprFast(v___x_2961_);
v___x_3037_ = lean_string_append(v___x_3035_, v___x_3036_);
lean_dec_ref(v___x_3036_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 0);
lean_ctor_set(v___x_2957_, 0, v___x_3037_);
v___x_3039_ = v___x_2957_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
lean_del_object(v___x_2957_);
goto v___jp_2963_;
}
}
else
{
lean_del_object(v___x_2957_);
goto v___jp_2963_;
}
v___jp_2963_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = lean_array_fget_borrowed(v_val_2960_, v___x_2964_);
lean_inc(v___x_2965_);
v___x_2966_ = l_Lean_Json_getNat_x3f(v___x_2965_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_val_2960_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
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
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_array_fget_borrowed(v_val_2960_, v___x_2976_);
lean_inc(v___x_2977_);
v___x_2978_ = l_Lean_Json_getNat_x3f(v___x_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_a_2975_);
lean_dec(v_val_2960_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
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
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_a_2987_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2988_ = lean_unsigned_to_nat(2u);
v___x_2989_ = lean_array_fget_borrowed(v_val_2960_, v___x_2988_);
lean_inc(v___x_2989_);
v___x_2990_ = l_Lean_Json_getNat_x3f(v___x_2989_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2987_);
lean_dec(v_a_2975_);
lean_dec(v_val_2960_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2999_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_3000_ = lean_unsigned_to_nat(3u);
v___x_3001_ = lean_array_fget_borrowed(v_val_2960_, v___x_3000_);
lean_inc(v___x_3001_);
v___x_3002_ = l_Lean_Json_getNat_x3f(v___x_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2999_);
lean_dec(v_a_2987_);
lean_dec(v_a_2975_);
lean_dec(v_val_2960_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_a_3011_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3012_ = lean_unsigned_to_nat(5u);
v___x_3013_ = lean_nat_dec_eq(v___x_2961_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3016_; 
lean_dec(v_val_2960_);
v___x_3014_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 4, v___x_3014_);
lean_ctor_set(v___x_2885_, 3, v_a_3011_);
lean_ctor_set(v___x_2885_, 2, v_a_2999_);
lean_ctor_set(v___x_2885_, 1, v_a_2987_);
lean_ctor_set(v___x_2885_, 0, v_a_2975_);
v___x_3016_ = v___x_2885_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v_a_2999_);
lean_ctor_set(v_reuseFailAlloc_3017_, 3, v_a_3011_);
lean_ctor_set(v_reuseFailAlloc_3017_, 4, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
v_a_2941_ = v___x_3016_;
goto v___jp_2940_;
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_array_fget(v_val_2960_, v___x_2962_);
lean_dec(v_val_2960_);
v___x_3019_ = l_Lean_Json_getStr_x3f(v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_3011_);
lean_dec(v_a_2999_);
lean_dec(v_a_2987_);
lean_dec(v_a_2975_);
lean_dec(v_a_2911_);
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
lean_del_object(v___x_2885_);
lean_dec(v_r_2883_);
lean_dec(v_v_2881_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; 
v_a_3028_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3019_, 1);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 4, v_a_3028_);
lean_ctor_set(v___x_2885_, 3, v_a_3011_);
lean_ctor_set(v___x_2885_, 2, v_a_2999_);
lean_ctor_set(v___x_2885_, 1, v_a_2987_);
lean_ctor_set(v___x_2885_, 0, v_a_2975_);
v___x_3030_ = v___x_2885_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_a_2999_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_a_3011_);
lean_ctor_set(v_reuseFailAlloc_3031_, 4, v_a_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
v_a_2941_ = v___x_3030_;
goto v___jp_2940_;
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
v___jp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2915_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2881_, v___x_2914_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_definition_x3f_2913_);
lean_dec(v_a_2911_);
lean_dec(v_a_2888_);
lean_dec(v_r_2883_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
else
{
lean_object* v_a_2924_; size_t v_sz_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
v_a_2924_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2915_, 1);
v_sz_2925_ = lean_array_size(v_a_2924_);
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2925_, v___x_2926_, v_a_2924_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_definition_x3f_2913_);
lean_dec(v_a_2911_);
lean_dec(v_a_2888_);
lean_dec(v_r_2883_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2936_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v_definition_x3f_2913_);
lean_ctor_set(v___x_2937_, 1, v_a_2936_);
v___x_2938_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2911_, v___x_2937_, v_a_2888_);
v_init_2878_ = v___x_2938_;
v_x_2879_ = v_r_2883_;
goto _start;
}
}
}
v___jp_2940_:
{
lean_object* v___x_2943_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v_a_2941_);
v___x_2943_ = v___x_2890_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
v_definition_x3f_2913_ = v___x_2943_;
goto v___jp_2912_;
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
lean_object* v___x_3045_; 
v___x_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_init_2878_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3046_, lean_object* v_k_3047_){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = l_Lean_Json_getObjValD(v_j_3046_, v_k_3047_);
v___x_3049_ = l_Lean_Json_getObj_x3f(v___x_3048_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
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
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3049_, 1);
v___x_3059_ = lean_box(1);
v___x_3060_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3059_, v_a_3058_);
return v___x_3060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3061_, lean_object* v_k_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3061_, v_k_3062_);
lean_dec_ref(v_k_3062_);
return v_res_3063_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = 1;
v___x_3070_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3071_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3073_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3074_ = lean_string_append(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3076_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3077_ = lean_string_append(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3079_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = 1;
v___x_3085_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3086_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3088_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3089_ = lean_string_append(v___x_3088_, v___x_3087_);
return v___x_3089_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3091_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3092_ = lean_string_append(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = 1;
v___x_3097_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3098_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3097_, v___x_3096_);
return v___x_3098_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3101_ = lean_string_append(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3103_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3104_ = lean_string_append(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3105_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3105_);
v___x_3107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3105_, v___x_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_json_3105_);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3113_ = lean_string_append(v___x_3112_, v_a_3108_);
lean_dec(v_a_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_json_3105_);
v_a_3118_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3107_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3107_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 0);
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
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
lean_object* v_a_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_a_3126_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3105_);
v___x_3128_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3105_, v___x_3127_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_a_3126_);
lean_dec(v_json_3105_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3134_ = lean_string_append(v___x_3133_, v_a_3129_);
lean_dec(v_a_3129_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3134_);
v___x_3136_ = v___x_3131_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_a_3126_);
lean_dec(v_json_3105_);
v_a_3139_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3128_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3128_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 0);
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
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
lean_object* v_a_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_a_3147_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3148_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3149_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3105_, v___x_3148_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3147_);
lean_dec(v_a_3126_);
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3159_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3159_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
v___x_3155_ = lean_string_append(v___x_3154_, v_a_3150_);
lean_dec(v_a_3150_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3155_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3147_);
lean_dec(v_a_3126_);
v_a_3160_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3149_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3149_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 0);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
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
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3176_; 
v_a_3168_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3170_ = v___x_3149_;
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3149_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3176_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3172_, 0, v_a_3126_);
lean_ctor_set(v___x_3172_, 1, v_a_3147_);
lean_ctor_set(v___x_3172_, 2, v_a_3168_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3177_, lean_object* v_k_3178_, lean_object* v_v_3179_, lean_object* v_t_3180_, lean_object* v_hl_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3178_, v_v_3179_, v_t_3180_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3183_, lean_object* v_k_3184_, lean_object* v_v_3185_, lean_object* v_t_3186_, lean_object* v_hl_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3184_, v_v_3185_, v_t_3186_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3191_, lean_object* v_x_3192_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 0)
{
lean_object* v_k_3193_; lean_object* v_v_3194_; lean_object* v_l_3195_; lean_object* v_r_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v_k_3193_ = lean_ctor_get(v_x_3192_, 1);
v_v_3194_ = lean_ctor_get(v_x_3192_, 2);
v_l_3195_ = lean_ctor_get(v_x_3192_, 3);
v_r_3196_ = lean_ctor_get(v_x_3192_, 4);
v___x_3197_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3191_, v_r_3196_);
lean_inc(v_v_3194_);
lean_inc(v_k_3193_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_k_3193_);
lean_ctor_set(v___x_3198_, 1, v_v_3194_);
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
lean_ctor_set(v___x_3199_, 1, v___x_3197_);
v_init_3191_ = v___x_3199_;
v_x_3192_ = v_l_3195_;
goto _start;
}
else
{
return v_init_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3201_, v_x_3202_);
lean_dec(v_x_3202_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3204_, size_t v_i_3205_, lean_object* v_bs_3206_){
_start:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_usize_dec_lt(v_i_3205_, v_sz_3204_);
if (v___x_3207_ == 0)
{
return v_bs_3206_;
}
else
{
lean_object* v_v_3208_; lean_object* v___x_3209_; lean_object* v_bs_x27_3210_; size_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; 
v_v_3208_ = lean_array_uget(v_bs_3206_, v_i_3205_);
v___x_3209_ = lean_unsigned_to_nat(0u);
v_bs_x27_3210_ = lean_array_uset(v_bs_3206_, v_i_3205_, v___x_3209_);
v___x_3211_ = ((size_t)1ULL);
v___x_3212_ = lean_usize_add(v_i_3205_, v___x_3211_);
v___x_3213_ = lean_array_uset(v_bs_x27_3210_, v_i_3205_, v_v_3208_);
v_i_3205_ = v___x_3212_;
v_bs_3206_ = v___x_3213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3215_, lean_object* v_i_3216_, lean_object* v_bs_3217_){
_start:
{
size_t v_sz_boxed_3218_; size_t v_i_boxed_3219_; lean_object* v_res_3220_; 
v_sz_boxed_3218_ = lean_unbox_usize(v_sz_3215_);
lean_dec(v_sz_3215_);
v_i_boxed_3219_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_res_3220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3218_, v_i_boxed_3219_, v_bs_3217_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3221_){
_start:
{
size_t v_sz_3222_; size_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_sz_3222_ = lean_array_size(v_a_3221_);
v___x_3223_ = ((size_t)0ULL);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3222_, v___x_3223_, v_a_3221_);
v___x_3225_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_array_mk(v_a_3226_);
v___x_3228_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_box(0);
return v___x_3230_;
}
else
{
lean_object* v_val_3231_; lean_object* v___x_3232_; 
v_val_3231_ = lean_ctor_get(v_x_3229_, 0);
lean_inc(v_val_3231_);
lean_dec_ref_known(v_x_3229_, 1);
v___x_3232_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3231_);
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
if (lean_obj_tag(v_a_3233_) == 0)
{
lean_object* v___x_3235_; 
v___x_3235_ = l_List_reverse___redArg(v_a_3234_);
return v___x_3235_;
}
else
{
lean_object* v_head_3236_; lean_object* v_tail_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3247_; 
v_head_3236_ = lean_ctor_get(v_a_3233_, 0);
v_tail_3237_ = lean_ctor_get(v_a_3233_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_a_3233_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3239_ = v_a_3233_;
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_tail_3237_);
lean_inc(v_head_3236_);
lean_dec(v_a_3233_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = l_Lean_JsonNumber_fromNat(v_head_3236_);
v___x_3242_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v_a_3234_);
lean_ctor_set(v___x_3239_, 0, v___x_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_a_3234_);
v___x_3244_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
v_a_3233_ = v_tail_3237_;
v_a_3234_ = v___x_3244_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3248_, size_t v_i_3249_, lean_object* v_bs_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = lean_usize_dec_lt(v_i_3249_, v_sz_3248_);
if (v___x_3251_ == 0)
{
return v_bs_3250_;
}
else
{
lean_object* v_v_3252_; lean_object* v_startPosLine_3253_; lean_object* v_startPosCharacter_3254_; lean_object* v_endPosLine_3255_; lean_object* v_endPosCharacter_3256_; lean_object* v___x_3257_; lean_object* v_bs_x27_3258_; lean_object* v___y_3260_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_range_3270_; lean_object* v___x_3271_; 
v_v_3252_ = lean_array_uget(v_bs_3250_, v_i_3249_);
v_startPosLine_3253_ = lean_ctor_get(v_v_3252_, 0);
v_startPosCharacter_3254_ = lean_ctor_get(v_v_3252_, 1);
v_endPosLine_3255_ = lean_ctor_get(v_v_3252_, 2);
v_endPosCharacter_3256_ = lean_ctor_get(v_v_3252_, 3);
v___x_3257_ = lean_unsigned_to_nat(0u);
v_bs_x27_3258_ = lean_array_uset(v_bs_3250_, v_i_3249_, v___x_3257_);
v___x_3265_ = lean_box(0);
lean_inc(v_endPosCharacter_3256_);
v___x_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_endPosCharacter_3256_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
lean_inc(v_endPosLine_3255_);
v___x_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_endPosLine_3255_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
lean_inc(v_startPosCharacter_3254_);
v___x_3268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_startPosCharacter_3254_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
lean_inc(v_startPosLine_3253_);
v___x_3269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_startPosLine_3253_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v_range_3270_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3269_, v___x_3265_);
v___x_3271_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3252_);
lean_dec(v_v_3252_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = l_List_appendTR___redArg(v_range_3270_, v___x_3265_);
v___y_3260_ = v___x_3272_;
goto v___jp_3259_;
}
else
{
lean_object* v_val_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3282_; 
v_val_3273_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3275_ = v___x_3271_;
v_isShared_3276_ = v_isSharedCheck_3282_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_val_3273_);
lean_dec(v___x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3282_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 3);
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_val_3273_);
v___x_3278_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3265_);
v___x_3280_ = l_List_appendTR___redArg(v_range_3270_, v___x_3279_);
v___y_3260_ = v___x_3280_;
goto v___jp_3259_;
}
}
}
v___jp_3259_:
{
size_t v___x_3261_; size_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3261_ = ((size_t)1ULL);
v___x_3262_ = lean_usize_add(v_i_3249_, v___x_3261_);
v___x_3263_ = lean_array_uset(v_bs_x27_3258_, v_i_3249_, v___y_3260_);
v_i_3249_ = v___x_3262_;
v_bs_3250_ = v___x_3263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3283_, lean_object* v_i_3284_, lean_object* v_bs_3285_){
_start:
{
size_t v_sz_boxed_3286_; size_t v_i_boxed_3287_; lean_object* v_res_3288_; 
v_sz_boxed_3286_ = lean_unbox_usize(v_sz_3283_);
lean_dec(v_sz_3283_);
v_i_boxed_3287_ = lean_unbox_usize(v_i_3284_);
lean_dec(v_i_3284_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3286_, v_i_boxed_3287_, v_bs_3285_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3289_, size_t v_i_3290_, lean_object* v_bs_3291_){
_start:
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_usize_dec_lt(v_i_3290_, v_sz_3289_);
if (v___x_3292_ == 0)
{
return v_bs_3291_;
}
else
{
lean_object* v_v_3293_; lean_object* v___x_3294_; lean_object* v_bs_x27_3295_; lean_object* v___x_3296_; size_t v___x_3297_; size_t v___x_3298_; lean_object* v___x_3299_; 
v_v_3293_ = lean_array_uget(v_bs_3291_, v_i_3290_);
v___x_3294_ = lean_unsigned_to_nat(0u);
v_bs_x27_3295_ = lean_array_uset(v_bs_3291_, v_i_3290_, v___x_3294_);
v___x_3296_ = l_Lean_List_toJson___at___00Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3293_);
v___x_3297_ = ((size_t)1ULL);
v___x_3298_ = lean_usize_add(v_i_3290_, v___x_3297_);
v___x_3299_ = lean_array_uset(v_bs_x27_3295_, v_i_3290_, v___x_3296_);
v_i_3290_ = v___x_3298_;
v_bs_3291_ = v___x_3299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3301_, lean_object* v_i_3302_, lean_object* v_bs_3303_){
_start:
{
size_t v_sz_boxed_3304_; size_t v_i_boxed_3305_; lean_object* v_res_3306_; 
v_sz_boxed_3304_ = lean_unbox_usize(v_sz_3301_);
lean_dec(v_sz_3301_);
v_i_boxed_3305_ = lean_unbox_usize(v_i_3302_);
lean_dec(v_i_3302_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3304_, v_i_boxed_3305_, v_bs_3303_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3307_){
_start:
{
size_t v_sz_3308_; size_t v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_sz_3308_ = lean_array_size(v_a_3307_);
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3308_, v___x_3309_, v_a_3307_);
v___x_3311_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
if (lean_obj_tag(v_a_3312_) == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = l_List_reverse___redArg(v_a_3313_);
return v___x_3314_;
}
else
{
lean_object* v_head_3315_; lean_object* v_snd_3316_; lean_object* v_tail_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3386_; 
v_head_3315_ = lean_ctor_get(v_a_3312_, 0);
lean_inc(v_head_3315_);
v_snd_3316_ = lean_ctor_get(v_head_3315_, 1);
lean_inc(v_snd_3316_);
v_tail_3317_ = lean_ctor_get(v_a_3312_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3312_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_a_3312_, 0);
lean_dec(v_unused_3387_);
v___x_3319_ = v_a_3312_;
v_isShared_3320_ = v_isSharedCheck_3386_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_tail_3317_);
lean_dec(v_a_3312_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3386_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_fst_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3384_; 
v_fst_3321_ = lean_ctor_get(v_head_3315_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_head_3315_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v_head_3315_, 1);
lean_dec(v_unused_3385_);
v___x_3323_ = v_head_3315_;
v_isShared_3324_ = v_isSharedCheck_3384_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_fst_3321_);
lean_dec(v_head_3315_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3384_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v_definition_x3f_3325_; lean_object* v_usages_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3383_; 
v_definition_x3f_3325_ = lean_ctor_get(v_snd_3316_, 0);
v_usages_3326_ = lean_ctor_get(v_snd_3316_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_snd_3316_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3328_ = v_snd_3316_;
v_isShared_3329_ = v_isSharedCheck_3383_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_usages_3326_);
lean_inc(v_definition_x3f_3325_);
lean_dec(v_snd_3316_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3383_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; lean_object* v___y_3357_; 
v___x_3330_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3321_);
v___x_3331_ = l_Lean_Json_compress(v___x_3330_);
v___x_3332_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3325_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_box(0);
v___y_3334_ = v___x_3359_;
goto v___jp_3333_;
}
else
{
lean_object* v_val_3360_; lean_object* v_startPosLine_3361_; lean_object* v_startPosCharacter_3362_; lean_object* v_endPosLine_3363_; lean_object* v_endPosCharacter_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v_range_3370_; lean_object* v___x_3371_; 
v_val_3360_ = lean_ctor_get(v_definition_x3f_3325_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v_definition_x3f_3325_, 1);
v_startPosLine_3361_ = lean_ctor_get(v_val_3360_, 0);
v_startPosCharacter_3362_ = lean_ctor_get(v_val_3360_, 1);
v_endPosLine_3363_ = lean_ctor_get(v_val_3360_, 2);
v_endPosCharacter_3364_ = lean_ctor_get(v_val_3360_, 3);
v___x_3365_ = lean_box(0);
lean_inc(v_endPosCharacter_3364_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_endPosCharacter_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
lean_inc(v_endPosLine_3363_);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_endPosLine_3363_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_inc(v_startPosCharacter_3362_);
v___x_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_startPosCharacter_3362_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
lean_inc(v_startPosLine_3361_);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v_startPosLine_3361_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v_range_3370_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3369_, v___x_3365_);
v___x_3371_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3360_);
lean_dec(v_val_3360_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = l_List_appendTR___redArg(v_range_3370_, v___x_3365_);
v___y_3357_ = v___x_3372_;
goto v___jp_3356_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3382_; 
v_val_3373_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3375_ = v___x_3371_;
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v___x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 3);
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_val_3373_);
v___x_3378_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3365_);
v___x_3380_ = l_List_appendTR___redArg(v_range_3370_, v___x_3379_);
v___y_3357_ = v___x_3380_;
goto v___jp_3356_;
}
}
}
}
v___jp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3334_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v___x_3335_);
lean_ctor_set(v___x_3323_, 0, v___x_3332_);
v___x_3337_ = v___x_3323_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; size_t v_sz_3339_; size_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3338_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3339_ = lean_array_size(v_usages_3326_);
v___x_3340_ = ((size_t)0ULL);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3339_, v___x_3340_, v_usages_3326_);
v___x_3342_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3341_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3342_);
lean_ctor_set(v___x_3328_, 0, v___x_3338_);
v___x_3344_ = v___x_3328_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3345_ = lean_box(0);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 1, v___x_3345_);
lean_ctor_set(v___x_3319_, 0, v___x_3344_);
v___x_3347_ = v___x_3319_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3337_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_Json_mkObj(v___x_3348_);
lean_dec_ref_known(v___x_3348_, 2);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3331_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v_a_3313_);
v_a_3312_ = v_tail_3317_;
v_a_3313_ = v___x_3351_;
goto _start;
}
}
}
}
v___jp_3356_:
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___y_3357_);
v___y_3334_ = v___x_3358_;
goto v___jp_3333_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
if (lean_obj_tag(v_a_3388_) == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = l_List_reverse___redArg(v_a_3389_);
return v___x_3390_;
}
else
{
lean_object* v_head_3391_; lean_object* v_snd_3392_; lean_object* v_tail_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3445_; 
v_head_3391_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_head_3391_);
v_snd_3392_ = lean_ctor_get(v_head_3391_, 1);
lean_inc(v_snd_3392_);
v_tail_3393_ = lean_ctor_get(v_a_3388_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v_a_3388_, 0);
lean_dec(v_unused_3446_);
v___x_3395_ = v_a_3388_;
v_isShared_3396_ = v_isSharedCheck_3445_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_tail_3393_);
lean_dec(v_a_3388_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3445_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_fst_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3443_; 
v_fst_3397_ = lean_ctor_get(v_head_3391_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_head_3391_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; 
v_unused_3444_ = lean_ctor_get(v_head_3391_, 1);
lean_dec(v_unused_3444_);
v___x_3399_ = v_head_3391_;
v_isShared_3400_ = v_isSharedCheck_3443_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_fst_3397_);
lean_dec(v_head_3391_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3443_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v_rangeStartPosLine_3401_; lean_object* v_rangeStartPosCharacter_3402_; lean_object* v_rangeEndPosLine_3403_; lean_object* v_rangeEndPosCharacter_3404_; lean_object* v_selectionRangeStartPosLine_3405_; lean_object* v_selectionRangeStartPosCharacter_3406_; lean_object* v_selectionRangeEndPosLine_3407_; lean_object* v_selectionRangeEndPosCharacter_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v_rangeStartPosLine_3401_ = lean_ctor_get(v_snd_3392_, 0);
lean_inc(v_rangeStartPosLine_3401_);
v_rangeStartPosCharacter_3402_ = lean_ctor_get(v_snd_3392_, 1);
lean_inc(v_rangeStartPosCharacter_3402_);
v_rangeEndPosLine_3403_ = lean_ctor_get(v_snd_3392_, 2);
lean_inc(v_rangeEndPosLine_3403_);
v_rangeEndPosCharacter_3404_ = lean_ctor_get(v_snd_3392_, 3);
lean_inc(v_rangeEndPosCharacter_3404_);
v_selectionRangeStartPosLine_3405_ = lean_ctor_get(v_snd_3392_, 4);
lean_inc(v_selectionRangeStartPosLine_3405_);
v_selectionRangeStartPosCharacter_3406_ = lean_ctor_get(v_snd_3392_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3406_);
v_selectionRangeEndPosLine_3407_ = lean_ctor_get(v_snd_3392_, 6);
lean_inc(v_selectionRangeEndPosLine_3407_);
v_selectionRangeEndPosCharacter_3408_ = lean_ctor_get(v_snd_3392_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3408_);
lean_dec(v_snd_3392_);
v___x_3409_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3401_);
v___x_3410_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
v___x_3411_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3402_);
v___x_3412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
v___x_3413_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3403_);
v___x_3414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
v___x_3415_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3404_);
v___x_3416_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
v___x_3417_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3405_);
v___x_3418_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
v___x_3419_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3406_);
v___x_3420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
v___x_3421_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3407_);
v___x_3422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
v___x_3423_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3408_);
v___x_3424_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
v___x_3425_ = lean_unsigned_to_nat(8u);
v___x_3426_ = lean_mk_empty_array_with_capacity(v___x_3425_);
v___x_3427_ = lean_array_push(v___x_3426_, v___x_3410_);
v___x_3428_ = lean_array_push(v___x_3427_, v___x_3412_);
v___x_3429_ = lean_array_push(v___x_3428_, v___x_3414_);
v___x_3430_ = lean_array_push(v___x_3429_, v___x_3416_);
v___x_3431_ = lean_array_push(v___x_3430_, v___x_3418_);
v___x_3432_ = lean_array_push(v___x_3431_, v___x_3420_);
v___x_3433_ = lean_array_push(v___x_3432_, v___x_3422_);
v___x_3434_ = lean_array_push(v___x_3433_, v___x_3424_);
v___x_3435_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 1, v___x_3435_);
v___x_3437_ = v___x_3399_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_fst_3397_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v_a_3389_);
lean_ctor_set(v___x_3395_, 0, v___x_3437_);
v___x_3439_ = v___x_3395_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3389_);
v___x_3439_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
v_a_3388_ = v_tail_3393_;
v_a_3389_ = v___x_3439_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3447_, lean_object* v_x_3448_){
_start:
{
if (lean_obj_tag(v_x_3448_) == 0)
{
lean_object* v_k_3449_; lean_object* v_v_3450_; lean_object* v_l_3451_; lean_object* v_r_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_k_3449_ = lean_ctor_get(v_x_3448_, 1);
v_v_3450_ = lean_ctor_get(v_x_3448_, 2);
v_l_3451_ = lean_ctor_get(v_x_3448_, 3);
v_r_3452_ = lean_ctor_get(v_x_3448_, 4);
v___x_3453_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3447_, v_r_3452_);
lean_inc(v_v_3450_);
lean_inc(v_k_3449_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v_k_3449_);
lean_ctor_set(v___x_3454_, 1, v_v_3450_);
v___x_3455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
lean_ctor_set(v___x_3455_, 1, v___x_3453_);
v_init_3447_ = v___x_3455_;
v_x_3448_ = v_l_3451_;
goto _start;
}
else
{
return v_init_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3457_, lean_object* v_x_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3457_, v_x_3458_);
lean_dec(v_x_3458_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3460_){
_start:
{
lean_object* v_version_3461_; lean_object* v_references_3462_; lean_object* v_decls_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_version_3461_ = lean_ctor_get(v_x_3460_, 0);
lean_inc(v_version_3461_);
v_references_3462_ = lean_ctor_get(v_x_3460_, 1);
lean_inc(v_references_3462_);
v_decls_3463_ = lean_ctor_get(v_x_3460_, 2);
lean_inc(v_decls_3463_);
lean_dec_ref(v_x_3460_);
v___x_3464_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3465_ = l_Lean_JsonNumber_fromNat(v_version_3461_);
v___x_3466_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3464_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3471_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3468_, v_references_3462_);
lean_dec(v_references_3462_);
v___x_3472_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3471_, v___x_3468_);
v___x_3473_ = l_Lean_Json_mkObj(v___x_3472_);
lean_dec(v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3470_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3468_);
v___x_3476_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3477_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3468_, v_decls_3463_);
lean_dec(v_decls_3463_);
v___x_3478_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3477_, v___x_3468_);
v___x_3479_ = l_Lean_Json_mkObj(v___x_3478_);
lean_dec(v___x_3478_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3476_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3468_);
v___x_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v___x_3468_);
v___x_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3475_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3469_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3486_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3484_, v___x_3485_);
v___x_3487_ = l_Lean_Json_mkObj(v___x_3486_);
lean_dec(v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3490_, size_t v_i_3491_, lean_object* v_bs_3492_){
_start:
{
uint8_t v___x_3493_; 
v___x_3493_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; 
v___x_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3494_, 0, v_bs_3492_);
return v___x_3494_;
}
else
{
lean_object* v_v_3495_; lean_object* v___x_3496_; 
v_v_3495_ = lean_array_uget_borrowed(v_bs_3492_, v_i_3491_);
lean_inc(v_v_3495_);
v___x_3496_ = l_Lean_Json_getStr_x3f(v_v_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v_bs_3492_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3506_; lean_object* v_bs_x27_3507_; size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v_a_3505_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3506_ = lean_unsigned_to_nat(0u);
v_bs_x27_3507_ = lean_array_uset(v_bs_3492_, v_i_3491_, v___x_3506_);
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3491_, v___x_3508_);
v___x_3510_ = lean_array_uset(v_bs_x27_3507_, v_i_3491_, v_a_3505_);
v_i_3491_ = v___x_3509_;
v_bs_3492_ = v___x_3510_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3512_, lean_object* v_i_3513_, lean_object* v_bs_3514_){
_start:
{
size_t v_sz_boxed_3515_; size_t v_i_boxed_3516_; lean_object* v_res_3517_; 
v_sz_boxed_3515_ = lean_unbox_usize(v_sz_3512_);
lean_dec(v_sz_3512_);
v_i_boxed_3516_ = lean_unbox_usize(v_i_3513_);
lean_dec(v_i_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3515_, v_i_boxed_3516_, v_bs_3514_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3518_){
_start:
{
if (lean_obj_tag(v_x_3518_) == 4)
{
lean_object* v_elems_3519_; size_t v_sz_3520_; size_t v___x_3521_; lean_object* v___x_3522_; 
v_elems_3519_ = lean_ctor_get(v_x_3518_, 0);
lean_inc_ref(v_elems_3519_);
lean_dec_ref_known(v_x_3518_, 1);
v_sz_3520_ = lean_array_size(v_elems_3519_);
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3520_, v___x_3521_, v_elems_3519_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3523_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3524_ = lean_unsigned_to_nat(80u);
v___x_3525_ = l_Lean_Json_pretty(v_x_3518_, v___x_3524_);
v___x_3526_ = lean_string_append(v___x_3523_, v___x_3525_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3528_ = lean_string_append(v___x_3526_, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3530_, lean_object* v_k_3531_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = l_Lean_Json_getObjValD(v_j_3530_, v_k_3531_);
v___x_3533_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3534_, lean_object* v_k_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3534_, v_k_3535_);
lean_dec_ref(v_k_3535_);
return v_res_3536_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = 1;
v___x_3544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3544_, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3547_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3548_ = lean_string_append(v___x_3547_, v___x_3546_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = 1;
v___x_3552_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3556_ = lean_string_append(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3558_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3559_ = lean_string_append(v___x_3558_, v___x_3557_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3560_){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3560_, v___x_3561_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3572_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3572_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3572_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3568_ = lean_string_append(v___x_3567_, v_a_3563_);
lean_dec(v_a_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3568_);
v___x_3570_ = v___x_3565_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
else
{
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
v_a_3573_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3562_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3562_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 0);
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
v_a_3581_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3562_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3562_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3591_, size_t v_i_3592_, lean_object* v_bs_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3592_, v_sz_3591_);
if (v___x_3594_ == 0)
{
return v_bs_3593_;
}
else
{
lean_object* v_v_3595_; lean_object* v___x_3596_; lean_object* v_bs_x27_3597_; lean_object* v___x_3598_; size_t v___x_3599_; size_t v___x_3600_; lean_object* v___x_3601_; 
v_v_3595_ = lean_array_uget(v_bs_3593_, v_i_3592_);
v___x_3596_ = lean_unsigned_to_nat(0u);
v_bs_x27_3597_ = lean_array_uset(v_bs_3593_, v_i_3592_, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_v_3595_);
v___x_3599_ = ((size_t)1ULL);
v___x_3600_ = lean_usize_add(v_i_3592_, v___x_3599_);
v___x_3601_ = lean_array_uset(v_bs_x27_3597_, v_i_3592_, v___x_3598_);
v_i_3592_ = v___x_3600_;
v_bs_3593_ = v___x_3601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3603_, lean_object* v_i_3604_, lean_object* v_bs_3605_){
_start:
{
size_t v_sz_boxed_3606_; size_t v_i_boxed_3607_; lean_object* v_res_3608_; 
v_sz_boxed_3606_ = lean_unbox_usize(v_sz_3603_);
lean_dec(v_sz_3603_);
v_i_boxed_3607_ = lean_unbox_usize(v_i_3604_);
lean_dec(v_i_3604_);
v_res_3608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3606_, v_i_boxed_3607_, v_bs_3605_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3609_){
_start:
{
size_t v_sz_3610_; size_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_sz_3610_ = lean_array_size(v_a_3609_);
v___x_3611_ = ((size_t)0ULL);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3610_, v___x_3611_, v_a_3609_);
v___x_3613_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3614_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3615_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3616_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3614_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_box(0);
v___x_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3618_);
v___x_3621_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3622_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3620_, v___x_3621_);
v___x_3623_ = l_Lean_Json_mkObj(v___x_3622_);
lean_dec(v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3626_, lean_object* v_k_3627_){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = l_Lean_Json_getObjValD(v_j_3626_, v_k_3627_);
v___x_3629_ = l_Lean_Json_getStr_x3f(v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3630_, lean_object* v_k_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3630_, v_k_3631_);
lean_dec_ref(v_k_3631_);
return v_res_3632_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = 1;
v___x_3640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3640_, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3643_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3644_ = lean_string_append(v___x_3643_, v___x_3642_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = 1;
v___x_3648_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3649_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3651_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3652_ = lean_string_append(v___x_3651_, v___x_3650_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3654_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3655_ = lean_string_append(v___x_3654_, v___x_3653_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3656_){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3656_, v___x_3657_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3668_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3668_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3664_ = lean_string_append(v___x_3663_, v_a_3659_);
lean_dec(v_a_3659_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3664_);
v___x_3666_ = v___x_3661_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
else
{
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3658_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3658_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 0);
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3658_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3658_);
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
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3687_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_x_3687_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v___x_3691_);
v___x_3694_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3695_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3693_, v___x_3694_);
v___x_3696_ = l_Lean_Json_mkObj(v___x_3695_);
lean_dec(v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl(lean_object* v_x_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_obj_tag_nat(v_x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___impl___boxed(lean_object* v_x_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Lsp_OpenNamespace_ctorIdx___impl(v_x_3701_);
lean_dec_ref(v_x_3701_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3703_, lean_object* v_k_3704_){
_start:
{
if (lean_obj_tag(v_t_3703_) == 0)
{
lean_object* v_namespace_3705_; lean_object* v_exceptions_3706_; lean_object* v___x_3707_; 
v_namespace_3705_ = lean_ctor_get(v_t_3703_, 0);
lean_inc(v_namespace_3705_);
v_exceptions_3706_ = lean_ctor_get(v_t_3703_, 1);
lean_inc_ref(v_exceptions_3706_);
lean_dec_ref_known(v_t_3703_, 2);
v___x_3707_ = lean_apply_2(v_k_3704_, v_namespace_3705_, v_exceptions_3706_);
return v___x_3707_;
}
else
{
lean_object* v_from_3708_; lean_object* v_to_3709_; lean_object* v___x_3710_; 
v_from_3708_ = lean_ctor_get(v_t_3703_, 0);
lean_inc(v_from_3708_);
v_to_3709_ = lean_ctor_get(v_t_3703_, 1);
lean_inc(v_to_3709_);
lean_dec_ref_known(v_t_3703_, 2);
v___x_3710_ = lean_apply_2(v_k_3704_, v_from_3708_, v_to_3709_);
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3711_, lean_object* v_ctorIdx_3712_, lean_object* v_t_3713_, lean_object* v_h_3714_, lean_object* v_k_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3713_, v_k_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3717_, lean_object* v_ctorIdx_3718_, lean_object* v_t_3719_, lean_object* v_h_3720_, lean_object* v_k_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3717_, v_ctorIdx_3718_, v_t_3719_, v_h_3720_, v_k_3721_);
lean_dec(v_ctorIdx_3718_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3723_, lean_object* v_allExcept_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3723_, v_allExcept_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3726_, lean_object* v_t_3727_, lean_object* v_h_3728_, lean_object* v_allExcept_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3727_, v_allExcept_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3731_, lean_object* v_renamed_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3731_, v_renamed_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3734_, lean_object* v_t_3735_, lean_object* v_h_3736_, lean_object* v_renamed_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3735_, v_renamed_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3739_, size_t v_i_3740_, lean_object* v_bs_3741_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_usize_dec_lt(v_i_3740_, v_sz_3739_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_bs_3741_);
return v___x_3743_;
}
else
{
lean_object* v_v_3744_; lean_object* v___x_3745_; 
v_v_3744_ = lean_array_uget_borrowed(v_bs_3741_, v_i_3740_);
lean_inc(v_v_3744_);
v___x_3745_ = l_Lean_Name_fromJson_x3f(v_v_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v_bs_3741_);
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3755_; lean_object* v_bs_x27_3756_; size_t v___x_3757_; size_t v___x_3758_; lean_object* v___x_3759_; 
v_a_3754_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3755_ = lean_unsigned_to_nat(0u);
v_bs_x27_3756_ = lean_array_uset(v_bs_3741_, v_i_3740_, v___x_3755_);
v___x_3757_ = ((size_t)1ULL);
v___x_3758_ = lean_usize_add(v_i_3740_, v___x_3757_);
v___x_3759_ = lean_array_uset(v_bs_x27_3756_, v_i_3740_, v_a_3754_);
v_i_3740_ = v___x_3758_;
v_bs_3741_ = v___x_3759_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3761_, lean_object* v_i_3762_, lean_object* v_bs_3763_){
_start:
{
size_t v_sz_boxed_3764_; size_t v_i_boxed_3765_; lean_object* v_res_3766_; 
v_sz_boxed_3764_ = lean_unbox_usize(v_sz_3761_);
lean_dec(v_sz_3761_);
v_i_boxed_3765_ = lean_unbox_usize(v_i_3762_);
lean_dec(v_i_3762_);
v_res_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3764_, v_i_boxed_3765_, v_bs_3763_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 4)
{
lean_object* v_elems_3768_; size_t v_sz_3769_; size_t v___x_3770_; lean_object* v___x_3771_; 
v_elems_3768_ = lean_ctor_get(v_x_3767_, 0);
lean_inc_ref(v_elems_3768_);
lean_dec_ref_known(v_x_3767_, 1);
v_sz_3769_ = lean_array_size(v_elems_3768_);
v___x_3770_ = ((size_t)0ULL);
v___x_3771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3769_, v___x_3770_, v_elems_3768_);
return v___x_3771_;
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3772_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3773_ = lean_unsigned_to_nat(80u);
v___x_3774_ = l_Lean_Json_pretty(v_x_3767_, v___x_3773_);
v___x_3775_ = lean_string_append(v___x_3772_, v___x_3774_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3777_ = lean_string_append(v___x_3775_, v___x_3776_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3813_){
_start:
{
lean_object* v___x_3814_; 
lean_inc(v_json_3813_);
v___x_3814_ = l_Lean_Json_getTag_x3f(v_json_3813_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v___x_3815_; 
lean_dec(v_json_3813_);
v___x_3815_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3815_;
}
else
{
lean_object* v_val_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v_val_3816_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_val_3816_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3817_ = lean_box(0);
v___x_3818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3819_ = lean_string_dec_eq(v_val_3816_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3820_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3821_ = lean_string_dec_eq(v_val_3816_, v___x_3820_);
lean_dec(v_val_3816_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; 
lean_dec(v_json_3813_);
v___x_3822_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3822_;
}
else
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3823_ = lean_unsigned_to_nat(2u);
v___x_3824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3825_ = l_Lean_Json_parseCtorFields(v_json_3813_, v___x_3820_, v___x_3823_, v___x_3824_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v_a_3834_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3825_, 1);
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = lean_array_get_borrowed(v___x_3817_, v_a_3834_, v___x_3835_);
lean_inc(v___x_3836_);
v___x_3837_ = l_Lean_Name_fromJson_x3f(v___x_3836_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_a_3834_);
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_a_3846_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3837_, 1);
v___x_3847_ = lean_unsigned_to_nat(1u);
v___x_3848_ = lean_array_get(v___x_3817_, v_a_3834_, v___x_3847_);
lean_dec(v_a_3834_);
v___x_3849_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3848_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec(v_a_3846_);
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3866_; 
v_a_3858_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3860_ = v___x_3849_;
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3849_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3866_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3846_);
lean_ctor_set(v___x_3862_, 1, v_a_3858_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3862_);
v___x_3864_ = v___x_3860_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec(v_val_3816_);
v___x_3867_ = lean_unsigned_to_nat(2u);
v___x_3868_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3869_ = l_Lean_Json_parseCtorFields(v_json_3813_, v___x_3818_, v___x_3867_, v___x_3868_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3869_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3869_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_a_3878_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3879_ = lean_unsigned_to_nat(0u);
v___x_3880_ = lean_array_get_borrowed(v___x_3817_, v_a_3878_, v___x_3879_);
lean_inc(v___x_3880_);
v___x_3881_ = l_Lean_Name_fromJson_x3f(v___x_3880_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec(v_a_3878_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_a_3890_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_array_get(v___x_3817_, v_a_3878_, v___x_3891_);
lean_dec(v_a_3878_);
v___x_3893_ = l_Lean_Name_fromJson_x3f(v___x_3892_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec(v_a_3890_);
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3910_; 
v_a_3902_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3904_ = v___x_3893_;
v_isShared_3905_ = v_isSharedCheck_3910_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3893_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3910_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v_a_3890_);
lean_ctor_set(v___x_3906_, 1, v_a_3902_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3906_);
v___x_3908_ = v___x_3904_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3913_, size_t v_i_3914_, lean_object* v_bs_3915_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_usize_dec_lt(v_i_3914_, v_sz_3913_);
if (v___x_3916_ == 0)
{
return v_bs_3915_;
}
else
{
lean_object* v_v_3917_; lean_object* v___x_3918_; lean_object* v_bs_x27_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; size_t v___x_3922_; size_t v___x_3923_; lean_object* v___x_3924_; 
v_v_3917_ = lean_array_uget(v_bs_3915_, v_i_3914_);
v___x_3918_ = lean_unsigned_to_nat(0u);
v_bs_x27_3919_ = lean_array_uset(v_bs_3915_, v_i_3914_, v___x_3918_);
v___x_3920_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3917_, v___x_3916_);
v___x_3921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
v___x_3922_ = ((size_t)1ULL);
v___x_3923_ = lean_usize_add(v_i_3914_, v___x_3922_);
v___x_3924_ = lean_array_uset(v_bs_x27_3919_, v_i_3914_, v___x_3921_);
v_i_3914_ = v___x_3923_;
v_bs_3915_ = v___x_3924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3926_, lean_object* v_i_3927_, lean_object* v_bs_3928_){
_start:
{
size_t v_sz_boxed_3929_; size_t v_i_boxed_3930_; lean_object* v_res_3931_; 
v_sz_boxed_3929_ = lean_unbox_usize(v_sz_3926_);
lean_dec(v_sz_3926_);
v_i_boxed_3930_ = lean_unbox_usize(v_i_3927_);
lean_dec(v_i_3927_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3929_, v_i_boxed_3930_, v_bs_3928_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3932_){
_start:
{
size_t v_sz_3933_; size_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_sz_3933_ = lean_array_size(v_a_3932_);
v___x_3934_ = ((size_t)0ULL);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3933_, v___x_3934_, v_a_3932_);
v___x_3936_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3937_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 0)
{
lean_object* v_namespace_3938_; lean_object* v_exceptions_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3961_; 
v_namespace_3938_ = lean_ctor_get(v_x_3937_, 0);
v_exceptions_3939_ = lean_ctor_get(v_x_3937_, 1);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_x_3937_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3941_ = v_x_3937_;
v_isShared_3942_ = v_isSharedCheck_3961_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_exceptions_3939_);
lean_inc(v_namespace_3938_);
lean_dec(v_x_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3961_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3943_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3944_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3945_ = 1;
v___x_3946_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3938_, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v___x_3947_);
lean_ctor_set(v___x_3941_, 0, v___x_3944_);
v___x_3949_ = v___x_3941_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3950_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3951_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3939_);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_box(0);
v___x_3954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3949_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l_Lean_Json_mkObj(v___x_3955_);
lean_dec_ref_known(v___x_3955_, 2);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3943_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3953_);
v___x_3959_ = l_Lean_Json_mkObj(v___x_3958_);
lean_dec_ref_known(v___x_3958_, 2);
return v___x_3959_;
}
}
}
else
{
lean_object* v_from_3962_; lean_object* v_to_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3986_; 
v_from_3962_ = lean_ctor_get(v_x_3937_, 0);
v_to_3963_ = lean_ctor_get(v_x_3937_, 1);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_x_3937_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3965_ = v_x_3937_;
v_isShared_3966_ = v_isSharedCheck_3986_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_to_3963_);
lean_inc(v_from_3962_);
lean_dec(v_x_3937_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3986_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3968_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3969_ = 1;
v___x_3970_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3962_, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 0);
lean_ctor_set(v___x_3965_, 1, v___x_3971_);
lean_ctor_set(v___x_3965_, 0, v___x_3968_);
v___x_3973_ = v___x_3965_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3968_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3963_, v___x_3969_);
v___x_3976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3974_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3973_);
lean_ctor_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = l_Lean_Json_mkObj(v___x_3980_);
lean_dec_ref_known(v___x_3980_, 2);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3967_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
lean_ctor_set(v___x_3983_, 1, v___x_3978_);
v___x_3984_ = l_Lean_Json_mkObj(v___x_3983_);
lean_dec_ref_known(v___x_3983_, 2);
return v___x_3984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_bs_3991_){
_start:
{
uint8_t v___x_3992_; 
v___x_3992_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3993_, 0, v_bs_3991_);
return v___x_3993_;
}
else
{
lean_object* v_v_3994_; lean_object* v___x_3995_; 
v_v_3994_ = lean_array_uget_borrowed(v_bs_3991_, v_i_3990_);
lean_inc(v_v_3994_);
v___x_3995_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_3994_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_bs_3991_);
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4005_; lean_object* v_bs_x27_4006_; size_t v___x_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v_a_4004_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_3995_, 1);
v___x_4005_ = lean_unsigned_to_nat(0u);
v_bs_x27_4006_ = lean_array_uset(v_bs_3991_, v_i_3990_, v___x_4005_);
v___x_4007_ = ((size_t)1ULL);
v___x_4008_ = lean_usize_add(v_i_3990_, v___x_4007_);
v___x_4009_ = lean_array_uset(v_bs_x27_4006_, v_i_3990_, v_a_4004_);
v_i_3990_ = v___x_4008_;
v_bs_3991_ = v___x_4009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4011_, lean_object* v_i_4012_, lean_object* v_bs_4013_){
_start:
{
size_t v_sz_boxed_4014_; size_t v_i_boxed_4015_; lean_object* v_res_4016_; 
v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4011_);
lean_dec(v_sz_4011_);
v_i_boxed_4015_ = lean_unbox_usize(v_i_4012_);
lean_dec(v_i_4012_);
v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4014_, v_i_boxed_4015_, v_bs_4013_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4017_){
_start:
{
if (lean_obj_tag(v_x_4017_) == 4)
{
lean_object* v_elems_4018_; size_t v_sz_4019_; size_t v___x_4020_; lean_object* v___x_4021_; 
v_elems_4018_ = lean_ctor_get(v_x_4017_, 0);
lean_inc_ref(v_elems_4018_);
lean_dec_ref_known(v_x_4017_, 1);
v_sz_4019_ = lean_array_size(v_elems_4018_);
v___x_4020_ = ((size_t)0ULL);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4019_, v___x_4020_, v_elems_4018_);
return v___x_4021_;
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4022_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4023_ = lean_unsigned_to_nat(80u);
v___x_4024_ = l_Lean_Json_pretty(v_x_4017_, v___x_4023_);
v___x_4025_ = lean_string_append(v___x_4022_, v___x_4024_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4027_ = lean_string_append(v___x_4025_, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4029_, lean_object* v_k_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = l_Lean_Json_getObjValD(v_j_4029_, v_k_4030_);
v___x_4032_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4033_, lean_object* v_k_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4033_, v_k_4034_);
lean_dec_ref(v_k_4034_);
return v_res_4035_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = 1;
v___x_4043_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4043_, v___x_4042_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4046_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4047_ = lean_string_append(v___x_4046_, v___x_4045_);
return v___x_4047_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = 1;
v___x_4051_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4052_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4051_, v___x_4050_);
return v___x_4052_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4054_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4055_ = lean_string_append(v___x_4054_, v___x_4053_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4057_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4058_ = lean_string_append(v___x_4057_, v___x_4056_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = 1;
v___x_4063_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4064_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4063_, v___x_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4066_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4067_ = lean_string_append(v___x_4066_, v___x_4065_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4070_ = lean_string_append(v___x_4069_, v___x_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4071_);
v___x_4073_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4071_, v___x_4072_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_json_4071_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4083_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4078_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4079_ = lean_string_append(v___x_4078_, v_a_4074_);
lean_dec(v_a_4074_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4079_);
v___x_4081_ = v___x_4076_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_json_4071_);
v_a_4084_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4073_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4073_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set_tag(v___x_4086_, 0);
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_a_4092_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4093_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4071_, v___x_4093_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4092_);
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4097_ = v___x_4094_;
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
v___x_4099_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4100_ = lean_string_append(v___x_4099_, v_a_4095_);
lean_dec(v_a_4095_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4100_);
v___x_4102_ = v___x_4097_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
else
{
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_a_4092_);
v_a_4105_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4094_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4094_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set_tag(v___x_4107_, 0);
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4121_; 
v_a_4113_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4115_ = v___x_4094_;
v_isShared_4116_ = v_isSharedCheck_4121_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4094_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4121_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4092_);
lean_ctor_set(v___x_4117_, 1, v_a_4113_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4117_);
v___x_4119_ = v___x_4115_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4124_, size_t v_i_4125_, lean_object* v_bs_4126_){
_start:
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_usize_dec_lt(v_i_4125_, v_sz_4124_);
if (v___x_4127_ == 0)
{
return v_bs_4126_;
}
else
{
lean_object* v_v_4128_; lean_object* v___x_4129_; lean_object* v_bs_x27_4130_; lean_object* v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
v_v_4128_ = lean_array_uget(v_bs_4126_, v_i_4125_);
v___x_4129_ = lean_unsigned_to_nat(0u);
v_bs_x27_4130_ = lean_array_uset(v_bs_4126_, v_i_4125_, v___x_4129_);
v___x_4131_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4128_);
v___x_4132_ = ((size_t)1ULL);
v___x_4133_ = lean_usize_add(v_i_4125_, v___x_4132_);
v___x_4134_ = lean_array_uset(v_bs_x27_4130_, v_i_4125_, v___x_4131_);
v_i_4125_ = v___x_4133_;
v_bs_4126_ = v___x_4134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4136_, lean_object* v_i_4137_, lean_object* v_bs_4138_){
_start:
{
size_t v_sz_boxed_4139_; size_t v_i_boxed_4140_; lean_object* v_res_4141_; 
v_sz_boxed_4139_ = lean_unbox_usize(v_sz_4136_);
lean_dec(v_sz_4136_);
v_i_boxed_4140_ = lean_unbox_usize(v_i_4137_);
lean_dec(v_i_4137_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4139_, v_i_boxed_4140_, v_bs_4138_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4142_){
_start:
{
size_t v_sz_4143_; size_t v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_sz_4143_ = lean_array_size(v_a_4142_);
v___x_4144_ = ((size_t)0ULL);
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4143_, v___x_4144_, v_a_4142_);
v___x_4146_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4147_){
_start:
{
lean_object* v_identifier_4148_; lean_object* v_openNamespaces_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4169_; 
v_identifier_4148_ = lean_ctor_get(v_x_4147_, 0);
v_openNamespaces_4149_ = lean_ctor_get(v_x_4147_, 1);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_x_4147_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4151_ = v_x_4147_;
v_isShared_4152_ = v_isSharedCheck_4169_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_openNamespaces_4149_);
lean_inc(v_identifier_4148_);
lean_dec(v_x_4147_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4169_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4153_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_identifier_4148_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 1, v___x_4154_);
lean_ctor_set(v___x_4151_, 0, v___x_4153_);
v___x_4156_ = v___x_4151_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4153_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4157_ = lean_box(0);
v___x_4158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4160_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4149_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
lean_ctor_set(v___x_4162_, 1, v___x_4157_);
v___x_4163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set(v___x_4163_, 1, v___x_4157_);
v___x_4164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4158_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4166_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4164_, v___x_4165_);
v___x_4167_ = l_Lean_Json_mkObj(v___x_4166_);
lean_dec(v___x_4166_);
return v___x_4167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4175_, lean_object* v_k_4176_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_Json_getObjValD(v_j_4175_, v_k_4176_);
switch(lean_obj_tag(v___x_4177_))
{
case 3:
{
lean_object* v_s_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4186_; 
v_s_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4186_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_s_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4186_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
lean_ctor_set_tag(v___x_4180_, 0);
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_s_4178_);
v___x_4183_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
return v___x_4184_;
}
}
}
case 2:
{
lean_object* v_n_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4195_; 
v_n_4187_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4189_ = v___x_4177_;
v_isShared_4190_ = v_isSharedCheck_4195_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_n_4187_);
lean_dec(v___x_4177_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4195_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
lean_ctor_set_tag(v___x_4189_, 1);
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_n_4187_);
v___x_4192_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
return v___x_4193_;
}
}
}
default: 
{
lean_object* v___x_4196_; 
lean_dec(v___x_4177_);
v___x_4196_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4197_, lean_object* v_k_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4197_, v_k_4198_);
lean_dec_ref(v_k_4198_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4200_, size_t v_i_4201_, lean_object* v_bs_4202_){
_start:
{
uint8_t v___x_4203_; 
v___x_4203_ = lean_usize_dec_lt(v_i_4201_, v_sz_4200_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4204_, 0, v_bs_4202_);
return v___x_4204_;
}
else
{
lean_object* v_v_4205_; lean_object* v___x_4206_; 
v_v_4205_ = lean_array_uget_borrowed(v_bs_4202_, v_i_4201_);
lean_inc(v_v_4205_);
v___x_4206_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_bs_4202_);
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
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
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v_bs_x27_4217_; size_t v___x_4218_; size_t v___x_4219_; lean_object* v___x_4220_; 
v_a_4215_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4206_, 1);
v___x_4216_ = lean_unsigned_to_nat(0u);
v_bs_x27_4217_ = lean_array_uset(v_bs_4202_, v_i_4201_, v___x_4216_);
v___x_4218_ = ((size_t)1ULL);
v___x_4219_ = lean_usize_add(v_i_4201_, v___x_4218_);
v___x_4220_ = lean_array_uset(v_bs_x27_4217_, v_i_4201_, v_a_4215_);
v_i_4201_ = v___x_4219_;
v_bs_4202_ = v___x_4220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4222_, lean_object* v_i_4223_, lean_object* v_bs_4224_){
_start:
{
size_t v_sz_boxed_4225_; size_t v_i_boxed_4226_; lean_object* v_res_4227_; 
v_sz_boxed_4225_ = lean_unbox_usize(v_sz_4222_);
lean_dec(v_sz_4222_);
v_i_boxed_4226_ = lean_unbox_usize(v_i_4223_);
lean_dec(v_i_4223_);
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4225_, v_i_boxed_4226_, v_bs_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4228_){
_start:
{
if (lean_obj_tag(v_x_4228_) == 4)
{
lean_object* v_elems_4229_; size_t v_sz_4230_; size_t v___x_4231_; lean_object* v___x_4232_; 
v_elems_4229_ = lean_ctor_get(v_x_4228_, 0);
lean_inc_ref(v_elems_4229_);
lean_dec_ref_known(v_x_4228_, 1);
v_sz_4230_ = lean_array_size(v_elems_4229_);
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4230_, v___x_4231_, v_elems_4229_);
return v___x_4232_;
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4233_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4234_ = lean_unsigned_to_nat(80u);
v___x_4235_ = l_Lean_Json_pretty(v_x_4228_, v___x_4234_);
v___x_4236_ = lean_string_append(v___x_4233_, v___x_4235_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4238_ = lean_string_append(v___x_4236_, v___x_4237_);
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
return v___x_4239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4240_, lean_object* v_k_4241_){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = l_Lean_Json_getObjValD(v_j_4240_, v_k_4241_);
v___x_4243_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4244_, lean_object* v_k_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4244_, v_k_4245_);
lean_dec_ref(v_k_4245_);
return v_res_4246_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = 1;
v___x_4254_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4254_, v___x_4253_);
return v___x_4255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4256_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4257_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4258_ = lean_string_append(v___x_4257_, v___x_4256_);
return v___x_4258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = 1;
v___x_4262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4262_, v___x_4261_);
return v___x_4263_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4265_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4266_ = lean_string_append(v___x_4265_, v___x_4264_);
return v___x_4266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4269_ = lean_string_append(v___x_4268_, v___x_4267_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = 1;
v___x_4274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4274_, v___x_4273_);
return v___x_4275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4278_ = lean_string_append(v___x_4277_, v___x_4276_);
return v___x_4278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4281_ = lean_string_append(v___x_4280_, v___x_4279_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4282_);
v___x_4284_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4282_, v___x_4283_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_json_4282_);
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4294_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4294_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4289_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4290_ = lean_string_append(v___x_4289_, v_a_4285_);
lean_dec(v_a_4285_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4290_);
v___x_4292_ = v___x_4287_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
else
{
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_dec(v_json_4282_);
v_a_4295_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4284_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4284_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 0);
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4303_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4284_, 1);
v___x_4304_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4305_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4282_, v___x_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v_a_4303_);
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4315_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4315_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4310_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4311_ = lean_string_append(v___x_4310_, v_a_4306_);
lean_dec(v_a_4306_);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v___x_4311_);
v___x_4313_ = v___x_4308_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
else
{
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v_a_4303_);
v_a_4316_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4305_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4305_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 0);
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4332_; 
v_a_4324_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4326_ = v___x_4305_;
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4305_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4332_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4330_; 
v___x_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_a_4303_);
lean_ctor_set(v___x_4328_, 1, v_a_4324_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4328_);
v___x_4330_ = v___x_4326_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4335_, size_t v_i_4336_, lean_object* v_bs_4337_){
_start:
{
uint8_t v___x_4338_; 
v___x_4338_ = lean_usize_dec_lt(v_i_4336_, v_sz_4335_);
if (v___x_4338_ == 0)
{
return v_bs_4337_;
}
else
{
lean_object* v_v_4339_; lean_object* v___x_4340_; lean_object* v_bs_x27_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; lean_object* v___x_4345_; 
v_v_4339_ = lean_array_uget(v_bs_4337_, v_i_4336_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v_bs_x27_4341_ = lean_array_uset(v_bs_4337_, v_i_4336_, v___x_4340_);
v___x_4342_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4339_);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_add(v_i_4336_, v___x_4343_);
v___x_4345_ = lean_array_uset(v_bs_x27_4341_, v_i_4336_, v___x_4342_);
v_i_4336_ = v___x_4344_;
v_bs_4337_ = v___x_4345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4347_, lean_object* v_i_4348_, lean_object* v_bs_4349_){
_start:
{
size_t v_sz_boxed_4350_; size_t v_i_boxed_4351_; lean_object* v_res_4352_; 
v_sz_boxed_4350_ = lean_unbox_usize(v_sz_4347_);
lean_dec(v_sz_4347_);
v_i_boxed_4351_ = lean_unbox_usize(v_i_4348_);
lean_dec(v_i_4348_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4350_, v_i_boxed_4351_, v_bs_4349_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4353_){
_start:
{
size_t v_sz_4354_; size_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_sz_4354_ = lean_array_size(v_a_4353_);
v___x_4355_ = ((size_t)0ULL);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4354_, v___x_4355_, v_a_4353_);
v___x_4357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4358_){
_start:
{
lean_object* v_sourceRequestID_4359_; lean_object* v_queries_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4398_; 
v_sourceRequestID_4359_ = lean_ctor_get(v_x_4358_, 0);
v_queries_4360_ = lean_ctor_get(v_x_4358_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_x_4358_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4362_ = v_x_4358_;
v_isShared_4363_ = v_isSharedCheck_4398_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_queries_4360_);
lean_inc(v_sourceRequestID_4359_);
lean_dec(v_x_4358_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4398_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4364_; lean_object* v___y_4366_; 
v___x_4364_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4359_))
{
case 0:
{
lean_object* v_s_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
v_s_4381_ = lean_ctor_get(v_sourceRequestID_4359_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_sourceRequestID_4359_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v_sourceRequestID_4359_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_s_4381_);
lean_dec(v_sourceRequestID_4359_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 3);
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_s_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
v___y_4366_ = v___x_4386_;
goto v___jp_4365_;
}
}
}
case 1:
{
lean_object* v_n_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
v_n_4389_ = lean_ctor_get(v_sourceRequestID_4359_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_sourceRequestID_4359_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v_sourceRequestID_4359_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_n_4389_);
lean_dec(v_sourceRequestID_4359_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set_tag(v___x_4391_, 2);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_n_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
v___y_4366_ = v___x_4394_;
goto v___jp_4365_;
}
}
}
default: 
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_box(0);
v___y_4366_ = v___x_4397_;
goto v___jp_4365_;
}
}
v___jp_4365_:
{
lean_object* v___x_4368_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 1, v___y_4366_);
lean_ctor_set(v___x_4362_, 0, v___x_4364_);
v___x_4368_ = v___x_4362_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4364_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v___y_4366_);
v___x_4368_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4369_ = lean_box(0);
v___x_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4372_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4360_);
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
lean_ctor_set(v___x_4374_, 1, v___x_4369_);
v___x_4375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
lean_ctor_set(v___x_4375_, 1, v___x_4369_);
v___x_4376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4370_);
lean_ctor_set(v___x_4376_, 1, v___x_4375_);
v___x_4377_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4378_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4376_, v___x_4377_);
v___x_4379_ = l_Lean_Json_mkObj(v___x_4378_);
lean_dec(v___x_4378_);
return v___x_4379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4401_, lean_object* v_k_4402_){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = l_Lean_Json_getObjValD(v_j_4401_, v_k_4402_);
v___x_4404_ = l_Lean_Name_fromJson_x3f(v___x_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4405_, lean_object* v_k_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4405_, v_k_4406_);
lean_dec_ref(v_k_4406_);
return v_res_4407_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = 1;
v___x_4415_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4419_ = lean_string_append(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4422_ = 1;
v___x_4423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4423_, v___x_4422_);
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4425_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4427_ = lean_string_append(v___x_4426_, v___x_4425_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4429_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4430_ = lean_string_append(v___x_4429_, v___x_4428_);
return v___x_4430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = 1;
v___x_4435_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4436_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4435_, v___x_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4438_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4439_ = lean_string_append(v___x_4438_, v___x_4437_);
return v___x_4439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4441_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4442_ = lean_string_append(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = 1;
v___x_4447_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4448_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4447_, v___x_4446_);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4450_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4451_ = lean_string_append(v___x_4450_, v___x_4449_);
return v___x_4451_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4453_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4454_ = lean_string_append(v___x_4453_, v___x_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4455_){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4455_);
v___x_4457_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4455_, v___x_4456_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_json_4455_);
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4460_ = v___x_4457_;
v_isShared_4461_ = v_isSharedCheck_4467_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4467_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4462_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4463_ = lean_string_append(v___x_4462_, v_a_4458_);
lean_dec(v_a_4458_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set(v___x_4460_, 0, v___x_4463_);
v___x_4465_ = v___x_4460_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
else
{
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_json_4455_);
v_a_4468_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4457_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4457_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set_tag(v___x_4470_, 0);
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v_a_4476_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4457_, 1);
v___x_4477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4455_);
v___x_4478_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4455_, v___x_4477_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_a_4476_);
lean_dec(v_json_4455_);
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4481_ = v___x_4478_;
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4478_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4483_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4484_ = lean_string_append(v___x_4483_, v_a_4479_);
lean_dec(v_a_4479_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 0, v___x_4484_);
v___x_4486_ = v___x_4481_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
else
{
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_a_4476_);
lean_dec(v_json_4455_);
v_a_4489_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4478_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4478_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set_tag(v___x_4491_, 0);
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v_a_4497_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4498_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4499_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4455_, v___x_4498_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_a_4497_);
lean_dec(v_a_4476_);
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4509_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4509_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4505_ = lean_string_append(v___x_4504_, v_a_4500_);
lean_dec(v_a_4500_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4505_);
v___x_4507_ = v___x_4502_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
else
{
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v_a_4497_);
lean_dec(v_a_4476_);
v_a_4510_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4499_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4499_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set_tag(v___x_4512_, 0);
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4527_; 
v_a_4518_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4520_ = v___x_4499_;
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4499_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; uint8_t v___x_4523_; lean_object* v___x_4525_; 
v___x_4522_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4522_, 0, v_a_4476_);
lean_ctor_set(v___x_4522_, 1, v_a_4497_);
v___x_4523_ = lean_unbox(v_a_4518_);
lean_dec(v_a_4518_);
lean_ctor_set_uint8(v___x_4522_, sizeof(void*)*2, v___x_4523_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4522_);
v___x_4525_ = v___x_4520_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4522_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4530_){
_start:
{
lean_object* v_module_4531_; lean_object* v_decl_4532_; uint8_t v_isExactMatch_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_module_4531_ = lean_ctor_get(v_x_4530_, 0);
lean_inc(v_module_4531_);
v_decl_4532_ = lean_ctor_get(v_x_4530_, 1);
lean_inc(v_decl_4532_);
v_isExactMatch_4533_ = lean_ctor_get_uint8(v_x_4530_, sizeof(void*)*2);
lean_dec_ref(v_x_4530_);
v___x_4534_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4535_ = 1;
v___x_4536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4531_, v___x_4535_);
v___x_4537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4534_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4532_, v___x_4535_);
v___x_4543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
v___x_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4541_);
lean_ctor_set(v___x_4544_, 1, v___x_4543_);
v___x_4545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
lean_ctor_set(v___x_4545_, 1, v___x_4539_);
v___x_4546_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4547_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4547_, 0, v_isExactMatch_4533_);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
v___x_4549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
lean_ctor_set(v___x_4549_, 1, v___x_4539_);
v___x_4550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
lean_ctor_set(v___x_4550_, 1, v___x_4539_);
v___x_4551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4545_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4540_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
v___x_4553_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4554_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4552_, v___x_4553_);
v___x_4555_ = l_Lean_Json_mkObj(v___x_4554_);
lean_dec(v___x_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4558_, size_t v_i_4559_, lean_object* v_bs_4560_){
_start:
{
uint8_t v___x_4561_; 
v___x_4561_ = lean_usize_dec_lt(v_i_4559_, v_sz_4558_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_bs_4560_);
return v___x_4562_;
}
else
{
lean_object* v_v_4563_; lean_object* v___x_4564_; 
v_v_4563_ = lean_array_uget_borrowed(v_bs_4560_, v_i_4559_);
lean_inc(v_v_4563_);
v___x_4564_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4563_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec_ref(v_bs_4560_);
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4564_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4574_; lean_object* v_bs_x27_4575_; size_t v___x_4576_; size_t v___x_4577_; lean_object* v___x_4578_; 
v_a_4573_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4564_, 1);
v___x_4574_ = lean_unsigned_to_nat(0u);
v_bs_x27_4575_ = lean_array_uset(v_bs_4560_, v_i_4559_, v___x_4574_);
v___x_4576_ = ((size_t)1ULL);
v___x_4577_ = lean_usize_add(v_i_4559_, v___x_4576_);
v___x_4578_ = lean_array_uset(v_bs_x27_4575_, v_i_4559_, v_a_4573_);
v_i_4559_ = v___x_4577_;
v_bs_4560_ = v___x_4578_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4580_, lean_object* v_i_4581_, lean_object* v_bs_4582_){
_start:
{
size_t v_sz_boxed_4583_; size_t v_i_boxed_4584_; lean_object* v_res_4585_; 
v_sz_boxed_4583_ = lean_unbox_usize(v_sz_4580_);
lean_dec(v_sz_4580_);
v_i_boxed_4584_ = lean_unbox_usize(v_i_4581_);
lean_dec(v_i_4581_);
v_res_4585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4583_, v_i_boxed_4584_, v_bs_4582_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4586_){
_start:
{
if (lean_obj_tag(v_x_4586_) == 4)
{
lean_object* v_elems_4587_; size_t v_sz_4588_; size_t v___x_4589_; lean_object* v___x_4590_; 
v_elems_4587_ = lean_ctor_get(v_x_4586_, 0);
lean_inc_ref(v_elems_4587_);
lean_dec_ref_known(v_x_4586_, 1);
v_sz_4588_ = lean_array_size(v_elems_4587_);
v___x_4589_ = ((size_t)0ULL);
v___x_4590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4588_, v___x_4589_, v_elems_4587_);
return v___x_4590_;
}
else
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4591_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4592_ = lean_unsigned_to_nat(80u);
v___x_4593_ = l_Lean_Json_pretty(v_x_4586_, v___x_4592_);
v___x_4594_ = lean_string_append(v___x_4591_, v___x_4593_);
lean_dec_ref(v___x_4593_);
v___x_4595_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4596_ = lean_string_append(v___x_4594_, v___x_4595_);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4598_, size_t v_i_4599_, lean_object* v_bs_4600_){
_start:
{
uint8_t v___x_4601_; 
v___x_4601_ = lean_usize_dec_lt(v_i_4599_, v_sz_4598_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
v___x_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4602_, 0, v_bs_4600_);
return v___x_4602_;
}
else
{
lean_object* v_v_4603_; lean_object* v___x_4604_; 
v_v_4603_ = lean_array_uget_borrowed(v_bs_4600_, v_i_4599_);
lean_inc(v_v_4603_);
v___x_4604_ = l_Lean_Array_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4603_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec_ref(v_bs_4600_);
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4614_; lean_object* v_bs_x27_4615_; size_t v___x_4616_; size_t v___x_4617_; lean_object* v___x_4618_; 
v_a_4613_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4604_, 1);
v___x_4614_ = lean_unsigned_to_nat(0u);
v_bs_x27_4615_ = lean_array_uset(v_bs_4600_, v_i_4599_, v___x_4614_);
v___x_4616_ = ((size_t)1ULL);
v___x_4617_ = lean_usize_add(v_i_4599_, v___x_4616_);
v___x_4618_ = lean_array_uset(v_bs_x27_4615_, v_i_4599_, v_a_4613_);
v_i_4599_ = v___x_4617_;
v_bs_4600_ = v___x_4618_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4620_, lean_object* v_i_4621_, lean_object* v_bs_4622_){
_start:
{
size_t v_sz_boxed_4623_; size_t v_i_boxed_4624_; lean_object* v_res_4625_; 
v_sz_boxed_4623_ = lean_unbox_usize(v_sz_4620_);
lean_dec(v_sz_4620_);
v_i_boxed_4624_ = lean_unbox_usize(v_i_4621_);
lean_dec(v_i_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4623_, v_i_boxed_4624_, v_bs_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4626_){
_start:
{
if (lean_obj_tag(v_x_4626_) == 4)
{
lean_object* v_elems_4627_; size_t v_sz_4628_; size_t v___x_4629_; lean_object* v___x_4630_; 
v_elems_4627_ = lean_ctor_get(v_x_4626_, 0);
lean_inc_ref(v_elems_4627_);
lean_dec_ref_known(v_x_4626_, 1);
v_sz_4628_ = lean_array_size(v_elems_4627_);
v___x_4629_ = ((size_t)0ULL);
v___x_4630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4628_, v___x_4629_, v_elems_4627_);
return v___x_4630_;
}
else
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4631_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4632_ = lean_unsigned_to_nat(80u);
v___x_4633_ = l_Lean_Json_pretty(v_x_4626_, v___x_4632_);
v___x_4634_ = lean_string_append(v___x_4631_, v___x_4633_);
lean_dec_ref(v___x_4633_);
v___x_4635_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4636_ = lean_string_append(v___x_4634_, v___x_4635_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4638_, lean_object* v_k_4639_){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = l_Lean_Json_getObjValD(v_j_4638_, v_k_4639_);
v___x_4641_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4642_, lean_object* v_k_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4642_, v_k_4643_);
lean_dec_ref(v_k_4643_);
return v_res_4644_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = 1;
v___x_4652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4653_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4652_, v___x_4651_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4655_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4656_ = lean_string_append(v___x_4655_, v___x_4654_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4659_ = 1;
v___x_4660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4660_, v___x_4659_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4664_ = lean_string_append(v___x_4663_, v___x_4662_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4667_ = lean_string_append(v___x_4666_, v___x_4665_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4668_){
_start:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4670_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4668_, v___x_4669_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4680_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4676_ = lean_string_append(v___x_4675_, v_a_4671_);
lean_dec(v_a_4671_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4676_);
v___x_4678_ = v___x_4673_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
else
{
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4670_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4670_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 0);
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v_a_4689_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4670_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4670_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4699_, size_t v_i_4700_, lean_object* v_bs_4701_){
_start:
{
uint8_t v___x_4702_; 
v___x_4702_ = lean_usize_dec_lt(v_i_4700_, v_sz_4699_);
if (v___x_4702_ == 0)
{
return v_bs_4701_;
}
else
{
lean_object* v_v_4703_; lean_object* v___x_4704_; lean_object* v_bs_x27_4705_; lean_object* v___x_4706_; size_t v___x_4707_; size_t v___x_4708_; lean_object* v___x_4709_; 
v_v_4703_ = lean_array_uget(v_bs_4701_, v_i_4700_);
v___x_4704_ = lean_unsigned_to_nat(0u);
v_bs_x27_4705_ = lean_array_uset(v_bs_4701_, v_i_4700_, v___x_4704_);
v___x_4706_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4703_);
v___x_4707_ = ((size_t)1ULL);
v___x_4708_ = lean_usize_add(v_i_4700_, v___x_4707_);
v___x_4709_ = lean_array_uset(v_bs_x27_4705_, v_i_4700_, v___x_4706_);
v_i_4700_ = v___x_4708_;
v_bs_4701_ = v___x_4709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4711_, lean_object* v_i_4712_, lean_object* v_bs_4713_){
_start:
{
size_t v_sz_boxed_4714_; size_t v_i_boxed_4715_; lean_object* v_res_4716_; 
v_sz_boxed_4714_ = lean_unbox_usize(v_sz_4711_);
lean_dec(v_sz_4711_);
v_i_boxed_4715_ = lean_unbox_usize(v_i_4712_);
lean_dec(v_i_4712_);
v_res_4716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4714_, v_i_boxed_4715_, v_bs_4713_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4717_){
_start:
{
size_t v_sz_4718_; size_t v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v_sz_4718_ = lean_array_size(v_a_4717_);
v___x_4719_ = ((size_t)0ULL);
v___x_4720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4718_, v___x_4719_, v_a_4717_);
v___x_4721_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4722_, size_t v_i_4723_, lean_object* v_bs_4724_){
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
v___x_4729_ = l_Lean_Array_toJson___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4726_);
v___x_4730_ = ((size_t)1ULL);
v___x_4731_ = lean_usize_add(v_i_4723_, v___x_4730_);
v___x_4732_ = lean_array_uset(v_bs_x27_4728_, v_i_4723_, v___x_4729_);
v_i_4723_ = v___x_4731_;
v_bs_4724_ = v___x_4732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4734_, lean_object* v_i_4735_, lean_object* v_bs_4736_){
_start:
{
size_t v_sz_boxed_4737_; size_t v_i_boxed_4738_; lean_object* v_res_4739_; 
v_sz_boxed_4737_ = lean_unbox_usize(v_sz_4734_);
lean_dec(v_sz_4734_);
v_i_boxed_4738_ = lean_unbox_usize(v_i_4735_);
lean_dec(v_i_4735_);
v_res_4739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4737_, v_i_boxed_4738_, v_bs_4736_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4740_){
_start:
{
size_t v_sz_4741_; size_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v_sz_4741_ = lean_array_size(v_a_4740_);
v___x_4742_ = ((size_t)0ULL);
v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4741_, v___x_4742_, v_a_4740_);
v___x_4744_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4745_){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4746_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4747_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4745_);
v___x_4748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = lean_box(0);
v___x_4750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
lean_ctor_set(v___x_4751_, 1, v___x_4749_);
v___x_4752_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4753_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4751_, v___x_4752_);
v___x_4754_ = l_Lean_Json_mkObj(v___x_4753_);
lean_dec(v___x_4753_);
return v___x_4754_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = 1;
v___x_4767_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4767_, v___x_4766_);
return v___x_4768_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4769_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4770_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4771_ = lean_string_append(v___x_4770_, v___x_4769_);
return v___x_4771_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4772_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4774_ = lean_string_append(v___x_4773_, v___x_4772_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4777_ = lean_string_append(v___x_4776_, v___x_4775_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4778_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4779_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4780_ = lean_string_append(v___x_4779_, v___x_4778_);
return v___x_4780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4782_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4783_ = lean_string_append(v___x_4782_, v___x_4781_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4784_){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4784_);
v___x_4786_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4784_, v___x_4785_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4796_; 
lean_dec(v_json_4784_);
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4789_ = v___x_4786_;
v_isShared_4790_ = v_isSharedCheck_4796_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4786_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4796_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4791_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4792_ = lean_string_append(v___x_4791_, v_a_4787_);
lean_dec(v_a_4787_);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v___x_4792_);
v___x_4794_ = v___x_4789_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4792_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
else
{
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
lean_dec(v_json_4784_);
v_a_4797_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4786_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4786_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
lean_ctor_set_tag(v___x_4799_, 0);
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v_a_4805_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4786_, 1);
v___x_4806_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4807_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4784_, v___x_4806_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4817_; 
lean_dec(v_a_4805_);
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4810_ = v___x_4807_;
v_isShared_4811_ = v_isSharedCheck_4817_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4807_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4817_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4812_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4813_ = lean_string_append(v___x_4812_, v_a_4808_);
lean_dec(v_a_4808_);
if (v_isShared_4811_ == 0)
{
lean_ctor_set(v___x_4810_, 0, v___x_4813_);
v___x_4815_ = v___x_4810_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
else
{
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec(v_a_4805_);
v_a_4818_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4807_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4807_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
lean_ctor_set_tag(v___x_4820_, 0);
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4834_; 
v_a_4826_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4828_ = v___x_4807_;
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4807_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4830_, 0, v_a_4805_);
lean_ctor_set(v___x_4830_, 1, v_a_4826_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 0, v___x_4830_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4837_){
_start:
{
lean_object* v_module_4838_; lean_object* v_decl_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4862_; 
v_module_4838_ = lean_ctor_get(v_x_4837_, 0);
v_decl_4839_ = lean_ctor_get(v_x_4837_, 1);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_x_4837_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4841_ = v_x_4837_;
v_isShared_4842_ = v_isSharedCheck_4862_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_decl_4839_);
lean_inc(v_module_4838_);
lean_dec(v_x_4837_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4862_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4843_; uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4848_; 
v___x_4843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4844_ = 1;
v___x_4845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4838_, v___x_4844_);
v___x_4846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 1, v___x_4846_);
lean_ctor_set(v___x_4841_, 0, v___x_4843_);
v___x_4848_ = v___x_4841_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4849_ = lean_box(0);
v___x_4850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4848_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4839_, v___x_4844_);
v___x_4853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
v___x_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4851_);
lean_ctor_set(v___x_4854_, 1, v___x_4853_);
v___x_4855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
lean_ctor_set(v___x_4855_, 1, v___x_4849_);
v___x_4856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
lean_ctor_set(v___x_4856_, 1, v___x_4849_);
v___x_4857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4850_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4859_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4857_, v___x_4858_);
v___x_4860_ = l_Lean_Json_mkObj(v___x_4859_);
lean_dec(v___x_4859_);
return v___x_4860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4865_, lean_object* v_k_4866_){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = l_Lean_Json_getObjValD(v_j_4865_, v_k_4866_);
v___x_4868_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4869_, lean_object* v_k_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4869_, v_k_4870_);
lean_dec_ref(v_k_4870_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4874_){
_start:
{
if (lean_obj_tag(v_x_4874_) == 0)
{
lean_object* v___x_4875_; 
v___x_4875_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4874_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4893_; 
v_a_4885_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4887_ = v___x_4876_;
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4876_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4889_, 0, v_a_4885_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4889_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4894_, lean_object* v_k_4895_){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = l_Lean_Json_getObjValD(v_j_4894_, v_k_4895_);
v___x_4897_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4898_, lean_object* v_k_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4898_, v_k_4899_);
lean_dec_ref(v_k_4899_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4903_){
_start:
{
if (lean_obj_tag(v_x_4903_) == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4904_;
}
else
{
lean_object* v___x_4905_; 
v___x_4905_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4903_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4905_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4905_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4922_; 
v_a_4914_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4916_ = v___x_4905_;
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4905_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4918_, 0, v_a_4914_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4918_);
v___x_4920_ = v___x_4916_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4923_, lean_object* v_k_4924_){
_start:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4925_ = l_Lean_Json_getObjValD(v_j_4923_, v_k_4924_);
v___x_4926_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4927_, lean_object* v_k_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4927_, v_k_4928_);
lean_dec_ref(v_k_4928_);
return v_res_4929_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = 1;
v___x_4937_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4938_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4937_, v___x_4936_);
return v___x_4938_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4939_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4940_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4941_ = lean_string_append(v___x_4940_, v___x_4939_);
return v___x_4941_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4945_ = 1;
v___x_4946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4947_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4946_, v___x_4945_);
return v___x_4947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4949_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4950_ = lean_string_append(v___x_4949_, v___x_4948_);
return v___x_4950_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4952_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4953_ = lean_string_append(v___x_4952_, v___x_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4957_ = 1;
v___x_4958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4958_, v___x_4957_);
return v___x_4959_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4961_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4962_ = lean_string_append(v___x_4961_, v___x_4960_);
return v___x_4962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4965_ = lean_string_append(v___x_4964_, v___x_4963_);
return v___x_4965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = 1;
v___x_4970_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4971_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4970_, v___x_4969_);
return v___x_4971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4973_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4974_ = lean_string_append(v___x_4973_, v___x_4972_);
return v___x_4974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4977_ = lean_string_append(v___x_4976_, v___x_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = 1;
v___x_4982_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4982_, v___x_4981_);
return v___x_4983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4985_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4986_ = lean_string_append(v___x_4985_, v___x_4984_);
return v___x_4986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4989_ = lean_string_append(v___x_4988_, v___x_4987_);
return v___x_4989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = 1;
v___x_4995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_4996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4995_, v___x_4994_);
return v___x_4996_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_4998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4999_ = lean_string_append(v___x_4998_, v___x_4997_);
return v___x_4999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5002_ = lean_string_append(v___x_5001_, v___x_5000_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5006_ = 1;
v___x_5007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5007_, v___x_5006_);
return v___x_5008_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5010_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5011_ = lean_string_append(v___x_5010_, v___x_5009_);
return v___x_5011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5012_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5014_ = lean_string_append(v___x_5013_, v___x_5012_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5015_){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5015_);
v___x_5017_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5015_, v___x_5016_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5027_; 
lean_dec(v_json_5015_);
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5027_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5027_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5022_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5023_ = lean_string_append(v___x_5022_, v_a_5018_);
lean_dec(v_a_5018_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 0, v___x_5023_);
v___x_5025_ = v___x_5020_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
else
{
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec(v_json_5015_);
v_a_5028_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5017_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5017_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
lean_ctor_set_tag(v___x_5030_, 0);
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v_a_5036_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5017_, 1);
v___x_5037_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5015_);
v___x_5038_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5015_, v___x_5037_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5048_; 
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5041_ = v___x_5038_;
v_isShared_5042_ = v_isSharedCheck_5048_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5038_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5048_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5046_; 
v___x_5043_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5044_ = lean_string_append(v___x_5043_, v_a_5039_);
lean_dec(v_a_5039_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5044_);
v___x_5046_ = v___x_5041_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
else
{
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5049_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_5038_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_5038_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
lean_ctor_set_tag(v___x_5051_, 0);
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v_a_5057_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5038_, 1);
v___x_5058_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5015_);
v___x_5059_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5015_, v___x_5058_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5069_; 
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5062_ = v___x_5059_;
v_isShared_5063_ = v_isSharedCheck_5069_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5059_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5069_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5067_; 
v___x_5064_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5065_ = lean_string_append(v___x_5064_, v_a_5060_);
lean_dec(v_a_5060_);
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 0, v___x_5065_);
v___x_5067_ = v___x_5062_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
else
{
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5070_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5059_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5059_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
lean_ctor_set_tag(v___x_5072_, 0);
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v_a_5078_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5059_, 1);
v___x_5079_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5015_);
v___x_5080_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5015_, v___x_5079_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5090_; 
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5083_ = v___x_5080_;
v_isShared_5084_ = v_isSharedCheck_5090_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5080_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5090_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5088_; 
v___x_5085_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5086_ = lean_string_append(v___x_5085_, v_a_5081_);
lean_dec(v_a_5081_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set(v___x_5083_, 0, v___x_5086_);
v___x_5088_ = v___x_5083_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
else
{
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5091_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5080_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5080_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 0);
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
v_a_5099_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5080_, 1);
v___x_5100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5015_);
v___x_5101_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5015_, v___x_5100_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_a_5099_);
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5104_ = v___x_5101_;
v_isShared_5105_ = v_isSharedCheck_5111_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5101_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5111_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5109_; 
v___x_5106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5107_ = lean_string_append(v___x_5106_, v_a_5102_);
lean_dec(v_a_5102_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v___x_5107_);
v___x_5109_ = v___x_5104_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
else
{
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_dec(v_a_5099_);
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
lean_dec(v_json_5015_);
v_a_5112_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___x_5101_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5101_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set_tag(v___x_5114_, 0);
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_a_5120_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5101_, 1);
v___x_5121_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5015_, v___x_5121_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5132_; 
lean_dec(v_a_5120_);
lean_dec(v_a_5099_);
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5132_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5132_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5130_; 
v___x_5127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5128_ = lean_string_append(v___x_5127_, v_a_5123_);
lean_dec(v_a_5123_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v___x_5128_);
v___x_5130_ = v___x_5125_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5128_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
else
{
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
lean_dec(v_a_5120_);
lean_dec(v_a_5099_);
lean_dec(v_a_5078_);
lean_dec(v_a_5057_);
lean_dec(v_a_5036_);
v_a_5133_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5122_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5122_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set_tag(v___x_5135_, 0);
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5151_; 
v_a_5141_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5143_ = v___x_5122_;
v_isShared_5144_ = v_isSharedCheck_5151_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5122_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5151_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; uint8_t v___x_5147_; lean_object* v___x_5149_; 
v___x_5145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5145_, 0, v_a_5036_);
lean_ctor_set(v___x_5145_, 1, v_a_5057_);
lean_ctor_set(v___x_5145_, 2, v_a_5078_);
lean_ctor_set(v___x_5145_, 3, v_a_5099_);
v___x_5146_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5146_, 0, v___x_5145_);
lean_ctor_set(v___x_5146_, 1, v_a_5120_);
v___x_5147_ = lean_unbox(v_a_5141_);
lean_dec(v_a_5141_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*2, v___x_5147_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5146_);
v___x_5149_ = v___x_5143_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v___x_5146_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5154_, lean_object* v_x_5155_){
_start:
{
if (lean_obj_tag(v_x_5155_) == 0)
{
lean_object* v___x_5156_; 
lean_dec_ref(v_k_5154_);
v___x_5156_ = lean_box(0);
return v___x_5156_;
}
else
{
lean_object* v_val_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; 
v_val_5157_ = lean_ctor_get(v_x_5155_, 0);
lean_inc(v_val_5157_);
lean_dec_ref_known(v_x_5155_, 1);
v___x_5158_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5157_);
v___x_5159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5159_, 0, v_k_5154_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
return v___x_5161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5162_, lean_object* v_x_5163_){
_start:
{
if (lean_obj_tag(v_x_5163_) == 0)
{
lean_object* v___x_5164_; 
lean_dec_ref(v_k_5162_);
v___x_5164_ = lean_box(0);
return v___x_5164_;
}
else
{
lean_object* v_val_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v_val_5165_ = lean_ctor_get(v_x_5163_, 0);
lean_inc(v_val_5165_);
lean_dec_ref_known(v_x_5163_, 1);
v___x_5166_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5165_);
v___x_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5167_, 0, v_k_5162_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = lean_box(0);
v___x_5169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5167_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
return v___x_5169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5170_){
_start:
{
lean_object* v_toLocationLink_5171_; lean_object* v_ident_x3f_5172_; uint8_t v_isDefault_5173_; lean_object* v_originSelectionRange_x3f_5174_; lean_object* v_targetUri_5175_; lean_object* v_targetRange_5176_; lean_object* v_targetSelectionRange_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v_toLocationLink_5171_ = lean_ctor_get(v_x_5170_, 0);
lean_inc_ref(v_toLocationLink_5171_);
v_ident_x3f_5172_ = lean_ctor_get(v_x_5170_, 1);
lean_inc(v_ident_x3f_5172_);
v_isDefault_5173_ = lean_ctor_get_uint8(v_x_5170_, sizeof(void*)*2);
lean_dec_ref(v_x_5170_);
v_originSelectionRange_x3f_5174_ = lean_ctor_get(v_toLocationLink_5171_, 0);
lean_inc(v_originSelectionRange_x3f_5174_);
v_targetUri_5175_ = lean_ctor_get(v_toLocationLink_5171_, 1);
lean_inc_ref(v_targetUri_5175_);
v_targetRange_5176_ = lean_ctor_get(v_toLocationLink_5171_, 2);
lean_inc_ref(v_targetRange_5176_);
v_targetSelectionRange_5177_ = lean_ctor_get(v_toLocationLink_5171_, 3);
lean_inc_ref(v_targetSelectionRange_5177_);
lean_dec_ref(v_toLocationLink_5171_);
v___x_5178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5179_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5178_, v_originSelectionRange_x3f_5174_);
v___x_5180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5181_, 0, v_targetUri_5175_);
v___x_5182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5180_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
v___x_5183_ = lean_box(0);
v___x_5184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5186_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5176_);
v___x_5187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5185_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5187_);
lean_ctor_set(v___x_5188_, 1, v___x_5183_);
v___x_5189_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5190_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5177_);
v___x_5191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5189_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
lean_ctor_set(v___x_5192_, 1, v___x_5183_);
v___x_5193_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5194_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5193_, v_ident_x3f_5172_);
v___x_5195_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5196_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5196_, 0, v_isDefault_5173_);
v___x_5197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5197_, 0, v___x_5195_);
lean_ctor_set(v___x_5197_, 1, v___x_5196_);
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
lean_ctor_set(v___x_5198_, 1, v___x_5183_);
v___x_5199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
lean_ctor_set(v___x_5199_, 1, v___x_5183_);
v___x_5200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5194_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5192_);
lean_ctor_set(v___x_5201_, 1, v___x_5200_);
v___x_5202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5188_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
v___x_5203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5184_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5179_);
lean_ctor_set(v___x_5204_, 1, v___x_5203_);
v___x_5205_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5206_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5204_, v___x_5205_);
v___x_5207_ = l_Lean_Json_mkObj(v___x_5206_);
lean_dec(v___x_5206_);
return v___x_5207_;
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

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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedRefIdent_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRefIdent_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRefIdent;
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDeclInfo___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent_default___closed__0(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent_default(void){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Lsp_instInhabitedRefIdent_default___closed__0, &l_Lean_Lsp_instInhabitedRefIdent_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRefIdent_default___closed__0);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRefIdent(void){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Lsp_instInhabitedRefIdent_default;
return v___x_186_;
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
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
v___x_602_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_601_);
lean_inc(v___x_602_);
v___x_603_ = l_Lean_Json_getNat_x3f(v___x_602_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_elems_588_);
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
v___x_614_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_613_);
lean_inc(v___x_614_);
v___x_615_ = l_Lean_Json_getNat_x3f(v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
v___x_626_ = lean_array_get_borrowed(v___x_586_, v_elems_588_, v___x_625_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Json_getNat_x3f(v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_624_);
lean_dec(v_a_612_);
lean_dec_ref(v_elems_588_);
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
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
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
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
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
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
lean_dec(v___x_586_);
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
lean_inc(v___x_586_);
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
lean_dec(v___x_586_);
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
lean_dec(v___x_586_);
v___x_706_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__2));
return v___x_706_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls___aux__1(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(1);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(1);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0(lean_object* v_f_712_, lean_object* v_a_713_, lean_object* v_b_714_, lean_object* v_c_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_a_713_);
lean_ctor_set(v___x_716_, 1, v_b_714_);
v___x_717_ = lean_apply_2(v_f_712_, v___x_716_, v_c_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg(lean_object* v_m_737_, lean_object* v_init_738_, lean_object* v_f_739_){
_start:
{
lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_a_743_; 
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_740_, 0, v_f_739_);
v___x_741_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_742_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_741_, v___f_740_, v_init_738_, v_m_737_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec(v___x_742_);
return v_a_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1(lean_object* v_00_u03b2_744_, lean_object* v_m_745_, lean_object* v_init_746_, lean_object* v_f_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_a_751_; 
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_748_, 0, v_f_747_);
v___x_749_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_750_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_749_, v___f_748_, v_init_746_, v_m_745_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec(v___x_750_);
return v_a_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(lean_object* v___y_752_, lean_object* v_init_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v_l_757_; lean_object* v_r_758_; lean_object* v___x_759_; 
v_k_755_ = lean_ctor_get(v_x_754_, 1);
v_v_756_ = lean_ctor_get(v_x_754_, 2);
v_l_757_ = lean_ctor_get(v_x_754_, 3);
v_r_758_ = lean_ctor_get(v_x_754_, 4);
lean_inc_ref(v___y_752_);
v___x_759_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_752_, v_init_753_, v_l_757_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_dec_ref(v___y_752_);
return v___x_759_;
}
else
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
lean_inc(v_v_756_);
lean_inc(v_k_755_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_k_755_);
lean_ctor_set(v___x_761_, 1, v_v_756_);
lean_inc_ref(v___y_752_);
v___x_762_ = lean_apply_2(v___y_752_, v___x_761_, v_a_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_dec_ref(v___y_752_);
return v___x_762_;
}
else
{
lean_object* v_a_763_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
v_init_753_ = v_a_763_;
v_x_754_ = v_r_758_;
goto _start;
}
}
}
else
{
lean_object* v___x_765_; 
lean_dec_ref(v___y_752_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v_init_753_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg___boxed(lean_object* v___y_766_, lean_object* v_init_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_766_, v_init_767_, v_x_768_);
lean_dec(v_x_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_774_; lean_object* v_a_775_; 
v___x_774_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_773_, v___y_772_, v___y_771_);
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
return v_a_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0___boxed(lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___lam__0(v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v_init_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___redArg(v___y_784_, v_init_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0___boxed(lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v_init_790_, lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Lsp_instForInIdDeclsProdStringDeclInfo_spec__0(v___y_788_, v___y_789_, v_init_790_, v_x_791_);
lean_dec(v_x_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_793_){
_start:
{
lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_837_; 
v_snd_794_ = lean_ctor_get(v_x_793_, 1);
v_fst_795_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_837_ == 0)
{
v___x_797_ = v_x_793_;
v_isShared_798_ = v_isSharedCheck_837_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_795_);
lean_dec(v_x_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_837_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_rangeStartPosLine_799_; lean_object* v_rangeStartPosCharacter_800_; lean_object* v_rangeEndPosLine_801_; lean_object* v_rangeEndPosCharacter_802_; lean_object* v_selectionRangeStartPosLine_803_; lean_object* v_selectionRangeStartPosCharacter_804_; lean_object* v_selectionRangeEndPosLine_805_; lean_object* v_selectionRangeEndPosCharacter_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v_rangeStartPosLine_799_ = lean_ctor_get(v_snd_794_, 0);
lean_inc(v_rangeStartPosLine_799_);
v_rangeStartPosCharacter_800_ = lean_ctor_get(v_snd_794_, 1);
lean_inc(v_rangeStartPosCharacter_800_);
v_rangeEndPosLine_801_ = lean_ctor_get(v_snd_794_, 2);
lean_inc(v_rangeEndPosLine_801_);
v_rangeEndPosCharacter_802_ = lean_ctor_get(v_snd_794_, 3);
lean_inc(v_rangeEndPosCharacter_802_);
v_selectionRangeStartPosLine_803_ = lean_ctor_get(v_snd_794_, 4);
lean_inc(v_selectionRangeStartPosLine_803_);
v_selectionRangeStartPosCharacter_804_ = lean_ctor_get(v_snd_794_, 5);
lean_inc(v_selectionRangeStartPosCharacter_804_);
v_selectionRangeEndPosLine_805_ = lean_ctor_get(v_snd_794_, 6);
lean_inc(v_selectionRangeEndPosLine_805_);
v_selectionRangeEndPosCharacter_806_ = lean_ctor_get(v_snd_794_, 7);
lean_inc(v_selectionRangeEndPosCharacter_806_);
lean_dec(v_snd_794_);
v___x_807_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_799_);
v___x_808_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_800_);
v___x_810_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_801_);
v___x_812_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_802_);
v___x_814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_803_);
v___x_816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_804_);
v___x_818_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_805_);
v___x_820_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
v___x_821_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_806_);
v___x_822_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
v___x_823_ = lean_unsigned_to_nat(8u);
v___x_824_ = lean_mk_empty_array_with_capacity(v___x_823_);
v___x_825_ = lean_array_push(v___x_824_, v___x_808_);
v___x_826_ = lean_array_push(v___x_825_, v___x_810_);
v___x_827_ = lean_array_push(v___x_826_, v___x_812_);
v___x_828_ = lean_array_push(v___x_827_, v___x_814_);
v___x_829_ = lean_array_push(v___x_828_, v___x_816_);
v___x_830_ = lean_array_push(v___x_829_, v___x_818_);
v___x_831_ = lean_array_push(v___x_830_, v___x_820_);
v___x_832_ = lean_array_push(v___x_831_, v___x_822_);
v___x_833_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_833_);
v___x_835_ = v___x_797_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_838_, lean_object* v_x2_839_, lean_object* v_x3_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_x1_838_);
lean_ctor_set(v___x_841_, 1, v_x2_839_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_x3_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_843_, lean_object* v___f_844_, lean_object* v_m_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_846_ = lean_box(0);
v___x_847_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_848_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_847_, v___f_843_, v___x_846_, v_m_845_);
v___x_849_ = l_List_mapTR_loop___redArg(v___f_844_, v___x_848_, v___x_846_);
v___x_850_ = l_Lean_Json_mkObj(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v_x_857_, lean_object* v_y_858_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_string_dec_lt(v_x_857_, v_y_858_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
v___x_860_ = lean_string_dec_eq(v_x_857_, v_y_858_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
v___x_861_ = 2;
return v___x_861_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = 1;
return v___x_862_;
}
}
else
{
uint8_t v___x_863_; 
v___x_863_ = 0;
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0___boxed(lean_object* v_x_864_, lean_object* v_y_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_Lsp_instFromJsonDecls___lam__0(v_x_864_, v_y_865_);
lean_dec_ref(v_y_865_);
lean_dec_ref(v_x_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___f_870_, lean_object* v_m_871_, lean_object* v_k_872_, lean_object* v_v_873_){
_start:
{
if (lean_obj_tag(v_v_873_) == 4)
{
lean_object* v_elems_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_993_; 
v_elems_874_ = lean_ctor_get(v_v_873_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_v_873_);
if (v_isSharedCheck_993_ == 0)
{
v___x_876_ = v_v_873_;
v_isShared_877_ = v_isSharedCheck_993_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_elems_874_);
lean_dec(v_v_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_993_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_array_get_size(v_elems_874_);
v___x_879_ = lean_unsigned_to_nat(8u);
v___x_880_ = lean_nat_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v___x_881_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_882_ = l_Nat_reprFast(v___x_878_);
v___x_883_ = lean_string_append(v___x_881_, v___x_882_);
lean_dec_ref(v___x_882_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
lean_ctor_set(v___x_876_, 0, v___x_883_);
v___x_885_ = v___x_876_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_del_object(v___x_876_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_888_);
lean_inc(v___x_889_);
v___x_890_ = l_Lean_Json_getNat_x3f(v___x_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_899_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_890_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_900_);
lean_inc(v___x_901_);
v___x_902_ = l_Lean_Json_getNat_x3f(v___x_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_a_911_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_902_);
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_912_);
lean_inc(v___x_913_);
v___x_914_ = l_Lean_Json_getNat_x3f(v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_a_923_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_914_);
v___x_924_ = lean_unsigned_to_nat(3u);
v___x_925_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_924_);
lean_inc(v___x_925_);
v___x_926_ = l_Lean_Json_getNat_x3f(v___x_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_a_923_);
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_935_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_926_);
v___x_936_ = lean_unsigned_to_nat(4u);
v___x_937_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_936_);
lean_inc(v___x_937_);
v___x_938_ = l_Lean_Json_getNat_x3f(v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_a_935_);
lean_dec(v_a_923_);
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_938_);
v___x_948_ = lean_unsigned_to_nat(5u);
v___x_949_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_948_);
lean_inc(v___x_949_);
v___x_950_ = l_Lean_Json_getNat_x3f(v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_a_947_);
lean_dec(v_a_935_);
lean_dec(v_a_923_);
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_959_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_950_);
v___x_960_ = lean_unsigned_to_nat(6u);
v___x_961_ = lean_array_get_borrowed(v___x_887_, v_elems_874_, v___x_960_);
lean_inc(v___x_961_);
v___x_962_ = l_Lean_Json_getNat_x3f(v___x_961_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_a_959_);
lean_dec(v_a_947_);
lean_dec(v_a_935_);
lean_dec(v_a_923_);
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_elems_874_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_971_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_962_);
v___x_972_ = lean_unsigned_to_nat(7u);
v___x_973_ = lean_array_get(v___x_887_, v_elems_874_, v___x_972_);
lean_dec_ref(v_elems_874_);
v___x_974_ = l_Lean_Json_getNat_x3f(v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_971_);
lean_dec(v_a_959_);
lean_dec(v_a_947_);
lean_dec(v_a_935_);
lean_dec(v_a_923_);
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_992_; 
v_a_983_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_992_ == 0)
{
v___x_985_ = v___x_974_;
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_974_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_987_, 0, v_a_899_);
lean_ctor_set(v___x_987_, 1, v_a_911_);
lean_ctor_set(v___x_987_, 2, v_a_923_);
lean_ctor_set(v___x_987_, 3, v_a_935_);
lean_ctor_set(v___x_987_, 4, v_a_947_);
lean_ctor_set(v___x_987_, 5, v_a_959_);
lean_ctor_set(v___x_987_, 6, v_a_971_);
lean_ctor_set(v___x_987_, 7, v_a_983_);
v___x_988_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_870_, v_k_872_, v___x_987_, v_m_871_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
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
lean_object* v___x_994_; 
lean_dec(v_v_873_);
lean_dec_ref(v_k_872_);
lean_dec(v_m_871_);
lean_dec_ref(v___f_870_);
v___x_994_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__2(lean_object* v___x_995_, lean_object* v___f_996_, lean_object* v_j_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Json_getObj_x3f(v_j_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v___f_996_);
lean_dec_ref(v___x_995_);
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_998_);
v___x_1008_ = lean_box(1);
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_995_, v___f_996_, v___x_1008_, v_a_1007_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_1041_, lean_object* v_parentDecl_x3f_1042_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_1042_) == 0)
{
lean_object* v_start_1043_; lean_object* v_end_1044_; lean_object* v_line_1045_; lean_object* v_character_1046_; lean_object* v_line_1047_; lean_object* v_character_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_start_1043_ = lean_ctor_get(v_range_1041_, 0);
v_end_1044_ = lean_ctor_get(v_range_1041_, 1);
v_line_1045_ = lean_ctor_get(v_start_1043_, 0);
v_character_1046_ = lean_ctor_get(v_start_1043_, 1);
v_line_1047_ = lean_ctor_get(v_end_1044_, 0);
v_character_1048_ = lean_ctor_get(v_end_1044_, 1);
v___x_1049_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_1048_);
lean_inc(v_line_1047_);
lean_inc(v_character_1046_);
lean_inc(v_line_1045_);
v___x_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1050_, 0, v_line_1045_);
lean_ctor_set(v___x_1050_, 1, v_character_1046_);
lean_ctor_set(v___x_1050_, 2, v_line_1047_);
lean_ctor_set(v___x_1050_, 3, v_character_1048_);
lean_ctor_set(v___x_1050_, 4, v___x_1049_);
return v___x_1050_;
}
else
{
lean_object* v_start_1051_; lean_object* v_end_1052_; lean_object* v_line_1053_; lean_object* v_character_1054_; lean_object* v_line_1055_; lean_object* v_character_1056_; lean_object* v_val_1057_; lean_object* v___x_1058_; 
v_start_1051_ = lean_ctor_get(v_range_1041_, 0);
v_end_1052_ = lean_ctor_get(v_range_1041_, 1);
v_line_1053_ = lean_ctor_get(v_start_1051_, 0);
v_character_1054_ = lean_ctor_get(v_start_1051_, 1);
v_line_1055_ = lean_ctor_get(v_end_1052_, 0);
v_character_1056_ = lean_ctor_get(v_end_1052_, 1);
v_val_1057_ = lean_ctor_get(v_parentDecl_x3f_1042_, 0);
lean_inc(v_val_1057_);
lean_inc(v_character_1056_);
lean_inc(v_line_1055_);
lean_inc(v_character_1054_);
lean_inc(v_line_1053_);
v___x_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1058_, 0, v_line_1053_);
lean_ctor_set(v___x_1058_, 1, v_character_1054_);
lean_ctor_set(v___x_1058_, 2, v_line_1055_);
lean_ctor_set(v___x_1058_, 3, v_character_1056_);
lean_ctor_set(v___x_1058_, 4, v_val_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_1059_, lean_object* v_parentDecl_x3f_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_1059_, v_parentDecl_x3f_1060_);
lean_dec(v_parentDecl_x3f_1060_);
lean_dec_ref(v_range_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1062_){
_start:
{
lean_object* v_startPosLine_1063_; lean_object* v_startPosCharacter_1064_; lean_object* v_endPosLine_1065_; lean_object* v_endPosCharacter_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_startPosLine_1063_ = lean_ctor_get(v_l_1062_, 0);
v_startPosCharacter_1064_ = lean_ctor_get(v_l_1062_, 1);
v_endPosLine_1065_ = lean_ctor_get(v_l_1062_, 2);
v_endPosCharacter_1066_ = lean_ctor_get(v_l_1062_, 3);
lean_inc(v_startPosCharacter_1064_);
lean_inc(v_startPosLine_1063_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_startPosLine_1063_);
lean_ctor_set(v___x_1067_, 1, v_startPosCharacter_1064_);
lean_inc(v_endPosCharacter_1066_);
lean_inc(v_endPosLine_1065_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_endPosLine_1065_);
lean_ctor_set(v___x_1068_, 1, v_endPosCharacter_1066_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1070_);
lean_dec_ref(v_l_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1072_){
_start:
{
lean_object* v_parentDecl_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_parentDecl_1073_ = lean_ctor_get(v_l_1072_, 4);
v___x_1074_ = lean_string_utf8_byte_size(v_parentDecl_1073_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_nat_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_inc_ref(v_parentDecl_1073_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_parentDecl_1073_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_box(0);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1079_);
lean_dec_ref(v_l_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = l_Lean_JsonNumber_fromNat(v_n_1081_);
v___x_1083_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1084_, lean_object* v_l_1085_){
_start:
{
lean_object* v_startPosLine_1086_; lean_object* v_startPosCharacter_1087_; lean_object* v_endPosLine_1088_; lean_object* v_endPosCharacter_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_range_1095_; lean_object* v___x_1096_; 
v_startPosLine_1086_ = lean_ctor_get(v_l_1085_, 0);
v_startPosCharacter_1087_ = lean_ctor_get(v_l_1085_, 1);
v_endPosLine_1088_ = lean_ctor_get(v_l_1085_, 2);
v_endPosCharacter_1089_ = lean_ctor_get(v_l_1085_, 3);
v___x_1090_ = lean_box(0);
lean_inc(v_endPosCharacter_1089_);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_endPosCharacter_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
lean_inc(v_endPosLine_1088_);
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_endPosLine_1088_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
lean_inc(v_startPosCharacter_1087_);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_startPosCharacter_1087_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
lean_inc(v_startPosLine_1086_);
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_startPosLine_1086_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v_range_1095_ = l_List_mapTR_loop___redArg(v___f_1084_, v___x_1094_, v___x_1090_);
v___x_1096_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1085_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = l_List_appendTR___redArg(v_range_1095_, v___x_1090_);
return v___x_1097_;
}
else
{
lean_object* v_val_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v_val_1098_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v___x_1096_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_val_1098_);
lean_dec(v___x_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 3);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1098_);
v___x_1103_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1090_);
v___x_1105_ = l_List_appendTR___redArg(v_range_1095_, v___x_1104_);
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1108_, lean_object* v_l_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1108_, v_l_1109_);
lean_dec_ref(v_l_1109_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_1(v_locationToList_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1116_, lean_object* v___f_1117_, lean_object* v_locationToList_1118_, lean_object* v_i_1119_){
_start:
{
lean_object* v_definition_x3f_1120_; lean_object* v_usages_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1153_; 
v_definition_x3f_1120_ = lean_ctor_get(v_i_1119_, 0);
v_usages_1121_ = lean_ctor_get(v_i_1119_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_i_1119_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1123_ = v_i_1119_;
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_usages_1121_);
lean_inc(v_definition_x3f_1120_);
lean_dec(v_i_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___y_1127_; 
v___x_1125_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1120_) == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_locationToList_1118_);
v___x_1143_ = lean_box(0);
v___y_1127_ = v___x_1143_;
goto v___jp_1126_;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_val_1144_ = lean_ctor_get(v_definition_x3f_1120_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_definition_x3f_1120_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v_definition_x3f_1120_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v_definition_x3f_1120_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_apply_1(v_locationToList_1118_, v_val_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
v___y_1127_ = v___x_1150_;
goto v___jp_1126_;
}
}
}
v___jp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_inc_ref(v___x_1116_);
v___x_1128_ = l_Option_toJson___redArg(v___x_1116_, v___y_1127_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1128_);
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1130_ = v___x_1123_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; size_t v_sz_1133_; size_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1131_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1132_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1133_ = lean_array_size(v_usages_1121_);
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1117_, v_sz_1133_, v___x_1134_, v_usages_1121_);
v___x_1136_ = l_Array_toJson___redArg(v___x_1116_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1131_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1130_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_Json_mkObj(v___x_1140_);
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1250_; 
v___x_1169_ = lean_array_get_size(v_a_1168_);
v___x_1170_ = lean_unsigned_to_nat(4u);
v___x_1250_ = lean_nat_dec_eq(v___x_1169_, v___x_1170_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_unsigned_to_nat(5u);
v___x_1252_ = lean_nat_dec_eq(v___x_1169_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1254_ = l_Nat_reprFast(v___x_1169_);
v___x_1255_ = lean_string_append(v___x_1253_, v___x_1254_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
else
{
goto v___jp_1171_;
}
}
else
{
goto v___jp_1171_;
}
v___jp_1171_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_array_fget_borrowed(v_a_1168_, v___x_1172_);
lean_inc(v___x_1173_);
v___x_1174_ = l_Lean_Json_getNat_x3f(v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1183_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1174_);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_array_fget_borrowed(v_a_1168_, v___x_1184_);
lean_inc(v___x_1185_);
v___x_1186_ = l_Lean_Json_getNat_x3f(v___x_1185_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_a_1183_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v___x_1186_);
v___x_1196_ = lean_unsigned_to_nat(2u);
v___x_1197_ = lean_array_fget_borrowed(v_a_1168_, v___x_1196_);
lean_inc(v___x_1197_);
v___x_1198_ = l_Lean_Json_getNat_x3f(v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1195_);
lean_dec(v_a_1183_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_a_1207_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1198_);
v___x_1208_ = lean_unsigned_to_nat(3u);
v___x_1209_ = lean_array_fget_borrowed(v_a_1168_, v___x_1208_);
lean_inc(v___x_1209_);
v___x_1210_ = l_Lean_Json_getNat_x3f(v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_a_1207_);
lean_dec(v_a_1195_);
lean_dec(v_a_1183_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1249_; 
v_a_1219_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1221_ = v___x_1210_;
v_isShared_1222_ = v_isSharedCheck_1249_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1210_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1249_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(5u);
v___x_1224_ = lean_nat_dec_eq(v___x_1169_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1183_);
lean_ctor_set(v___x_1226_, 1, v_a_1195_);
lean_ctor_set(v___x_1226_, 2, v_a_1207_);
lean_ctor_set(v___x_1226_, 3, v_a_1219_);
lean_ctor_set(v___x_1226_, 4, v___x_1225_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1226_);
v___x_1228_ = v___x_1221_;
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
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_1221_);
v___x_1230_ = lean_array_fget_borrowed(v_a_1168_, v___x_1170_);
lean_inc(v___x_1230_);
v___x_1231_ = l_Lean_Json_getStr_x3f(v___x_1230_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1219_);
lean_dec(v_a_1207_);
lean_dec(v_a_1195_);
lean_dec(v_a_1183_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
v_a_1240_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1242_ = v___x_1231_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1231_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1244_, 0, v_a_1183_);
lean_ctor_set(v___x_1244_, 1, v_a_1195_);
lean_ctor_set(v___x_1244_, 2, v_a_1207_);
lean_ctor_set(v___x_1244_, 3, v_a_1219_);
lean_ctor_set(v___x_1244_, 4, v_a_1240_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1257_);
lean_dec_ref(v_a_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___x_1261_, lean_object* v_toLocation_1262_, lean_object* v_j_1263_){
_start:
{
lean_object* v_definition_x3f_1265_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1263_);
v___x_1298_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1263_, v___x_1259_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_j_1263_);
lean_dec_ref(v_toLocation_1262_);
lean_dec_ref(v___x_1261_);
lean_dec_ref(v___x_1260_);
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
lean_object* v_a_1307_; 
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1298_);
if (lean_obj_tag(v_a_1307_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_box(0);
v_definition_x3f_1265_ = v___x_1308_;
goto v___jp_1264_;
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1326_; 
v_val_1309_ = lean_ctor_get(v_a_1307_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_a_1307_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1311_ = v_a_1307_;
v_isShared_1312_ = v_isSharedCheck_1326_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_dec(v_a_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1326_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; 
lean_inc_ref(v_toLocation_1262_);
v___x_1313_ = lean_apply_1(v_toLocation_1262_, v_val_1309_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1311_);
lean_dec(v_j_1263_);
lean_dec_ref(v_toLocation_1262_);
lean_dec_ref(v___x_1261_);
lean_dec_ref(v___x_1260_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; 
v_a_1322_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1313_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_a_1322_);
v___x_1324_ = v___x_1311_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
v_definition_x3f_1265_ = v___x_1324_;
goto v___jp_1264_;
}
}
}
}
}
v___jp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1267_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1263_, v___x_1260_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_definition_x3f_1265_);
lean_dec_ref(v_toLocation_1262_);
lean_dec_ref(v___x_1261_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_object* v_a_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1267_);
v_sz_1277_ = lean_array_size(v_a_1276_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1261_, v_toLocation_1262_, v_sz_1277_, v___x_1278_, v_a_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_definition_x3f_1265_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
v_a_1288_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1290_ = v___x_1279_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1279_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_definition_x3f_1265_);
lean_ctor_set(v___x_1292_, 1, v_a_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
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
lean_object* v___x_1341_; 
v___x_1341_ = lean_box(1);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_box(1);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1343_, lean_object* v_a_1344_, lean_object* v_b_1345_, lean_object* v_c_1346_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1344_);
lean_ctor_set(v___x_1347_, 1, v_b_1345_);
v___x_1348_ = lean_apply_2(v_f_1343_, v___x_1347_, v_c_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1349_, lean_object* v_____do__lift_1350_){
_start:
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v_____do__lift_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v_____do__lift_1350_);
v___x_1352_ = lean_apply_2(v_toPure_1349_, lean_box(0), v_a_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_map_1355_, lean_object* v_init_1356_, lean_object* v_f_1357_){
_start:
{
lean_object* v_toApplicative_1358_; lean_object* v_toBind_1359_; lean_object* v_toPure_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; 
v_toApplicative_1358_ = lean_ctor_get(v_inst_1353_, 0);
v_toBind_1359_ = lean_ctor_get(v_inst_1353_, 1);
lean_inc(v_toBind_1359_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1358_, 1);
lean_inc(v_toPure_1360_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1361_, 0, v_f_1357_);
v___x_1362_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1353_, v___f_1361_, v_init_1356_, v_map_1355_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1363_, 0, v_toPure_1360_);
v___x_1364_ = lean_apply_4(v_toBind_1359_, lean_box(0), lean_box(0), v___x_1362_, v___f_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1365_){
_start:
{
lean_object* v___f_1366_; 
v___f_1366_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1366_, 0, v_inst_1365_);
return v___f_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1367_, lean_object* v_inst_1368_){
_start:
{
lean_object* v___f_1369_; 
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1369_, 0, v_inst_1368_);
return v___f_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_startPosLine_1372_; lean_object* v_startPosCharacter_1373_; lean_object* v_endPosLine_1374_; lean_object* v_endPosCharacter_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_range_1381_; lean_object* v___x_1382_; 
v_startPosLine_1372_ = lean_ctor_get(v_x_1371_, 0);
v_startPosCharacter_1373_ = lean_ctor_get(v_x_1371_, 1);
v_endPosLine_1374_ = lean_ctor_get(v_x_1371_, 2);
v_endPosCharacter_1375_ = lean_ctor_get(v_x_1371_, 3);
v___x_1376_ = lean_box(0);
lean_inc(v_endPosCharacter_1375_);
v___x_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_endPosCharacter_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
lean_inc(v_endPosLine_1374_);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_endPosLine_1374_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_inc(v_startPosCharacter_1373_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_startPosCharacter_1373_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
lean_inc(v_startPosLine_1372_);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_startPosLine_1372_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v_range_1381_ = l_List_mapTR_loop___redArg(v___f_1370_, v___x_1380_, v___x_1376_);
v___x_1382_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1371_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = l_List_appendTR___redArg(v_range_1381_, v___x_1376_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
v_val_1384_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 3);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___x_1376_);
v___x_1391_ = l_List_appendTR___redArg(v_range_1381_, v___x_1390_);
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1394_, v_x_1395_);
lean_dec_ref(v_x_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1397_, lean_object* v___f_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_snd_1400_; lean_object* v_fst_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1462_; 
v_snd_1400_ = lean_ctor_get(v_x_1399_, 1);
v_fst_1401_ = lean_ctor_get(v_x_1399_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1399_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1403_ = v_x_1399_;
v_isShared_1404_ = v_isSharedCheck_1462_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_snd_1400_);
lean_inc(v_fst_1401_);
lean_dec(v_x_1399_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1462_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_definition_x3f_1405_; lean_object* v_usages_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1461_; 
v_definition_x3f_1405_ = lean_ctor_get(v_snd_1400_, 0);
v_usages_1406_ = lean_ctor_get(v_snd_1400_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_snd_1400_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1408_ = v_snd_1400_;
v_isShared_1409_ = v_isSharedCheck_1461_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_usages_1406_);
lean_inc(v_definition_x3f_1405_);
lean_dec(v_snd_1400_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1461_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___y_1415_; lean_object* v___y_1435_; 
v___x_1410_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1401_);
v___x_1411_ = l_Lean_Json_compress(v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1413_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1405_) == 0)
{
lean_object* v___x_1437_; 
lean_dec_ref(v___f_1398_);
v___x_1437_ = lean_box(0);
v___y_1415_ = v___x_1437_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1438_; lean_object* v_startPosLine_1439_; lean_object* v_startPosCharacter_1440_; lean_object* v_endPosLine_1441_; lean_object* v_endPosCharacter_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_range_1448_; lean_object* v___x_1449_; 
v_val_1438_ = lean_ctor_get(v_definition_x3f_1405_, 0);
lean_inc(v_val_1438_);
lean_dec_ref(v_definition_x3f_1405_);
v_startPosLine_1439_ = lean_ctor_get(v_val_1438_, 0);
v_startPosCharacter_1440_ = lean_ctor_get(v_val_1438_, 1);
v_endPosLine_1441_ = lean_ctor_get(v_val_1438_, 2);
v_endPosCharacter_1442_ = lean_ctor_get(v_val_1438_, 3);
v___x_1443_ = lean_box(0);
lean_inc(v_endPosCharacter_1442_);
v___x_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_endPosCharacter_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
lean_inc(v_endPosLine_1441_);
v___x_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_endPosLine_1441_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
lean_inc(v_startPosCharacter_1440_);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_startPosCharacter_1440_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
lean_inc(v_startPosLine_1439_);
v___x_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_startPosLine_1439_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v_range_1448_ = l_List_mapTR_loop___redArg(v___f_1398_, v___x_1447_, v___x_1443_);
v___x_1449_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1438_);
lean_dec(v_val_1438_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = l_List_appendTR___redArg(v_range_1448_, v___x_1443_);
v___y_1435_ = v___x_1450_;
goto v___jp_1434_;
}
else
{
lean_object* v_val_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
v_val_1451_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1449_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_val_1451_);
lean_dec(v___x_1449_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 3);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_val_1451_);
v___x_1456_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v___x_1443_);
v___x_1458_ = l_List_appendTR___redArg(v_range_1448_, v___x_1457_);
v___y_1435_ = v___x_1458_;
goto v___jp_1434_;
}
}
}
}
v___jp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = l_Option_toJson___redArg(v___x_1412_, v___y_1415_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 1, v___x_1416_);
lean_ctor_set(v___x_1403_, 0, v___x_1413_);
v___x_1418_ = v___x_1403_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; size_t v_sz_1421_; size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1419_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1420_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v_sz_1421_ = lean_array_size(v_usages_1406_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1420_, v___f_1397_, v_sz_1421_, v___x_1422_, v_usages_1406_);
v___x_1424_ = l_Array_toJson___redArg(v___x_1412_, v___x_1423_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1424_);
lean_ctor_set(v___x_1408_, 0, v___x_1419_);
v___x_1426_ = v___x_1408_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1418_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_Json_mkObj(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1411_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
return v___x_1431_;
}
}
}
v___jp_1434_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___y_1435_);
v___y_1415_ = v___x_1436_;
goto v___jp_1414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1463_, lean_object* v_x2_1464_, lean_object* v_x3_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_x1_1463_);
lean_ctor_set(v___x_1466_, 1, v_x2_1464_);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_x3_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1468_, lean_object* v___f_1469_, lean_object* v_m_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___aux__1___redArg___closed__9));
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1472_, v___f_1468_, v___x_1471_, v_m_1470_);
v___x_1474_ = l_List_mapTR_loop___redArg(v___f_1469_, v___x_1473_, v___x_1471_);
v___x_1475_ = l_Lean_Json_mkObj(v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1486_, lean_object* v_m_1487_, lean_object* v_k_1488_, lean_object* v_v_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Json_parse(v_k_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1490_);
v___x_1500_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_a_1509_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1500_);
v___x_1510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__11));
v___x_1511_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1512_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1489_);
v___x_1513_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1489_, v___x_1511_, v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1643_; 
v_a_1522_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1524_ = v___x_1513_;
v_isShared_1525_ = v_isSharedCheck_1643_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1513_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1643_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v_definition_x3f_1528_; lean_object* v_a_1563_; 
v___x_1526_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1522_) == 0)
{
lean_object* v___x_1565_; 
lean_del_object(v___x_1524_);
v___x_1565_ = lean_box(0);
v_definition_x3f_1528_ = v___x_1565_;
goto v___jp_1527_;
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1634_; 
v_val_1566_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_val_1566_);
lean_dec_ref(v_a_1522_);
v___x_1567_ = lean_array_get_size(v_val_1566_);
v___x_1568_ = lean_unsigned_to_nat(4u);
v___x_1634_ = lean_nat_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(5u);
v___x_1636_ = lean_nat_dec_eq(v___x_1567_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_val_1566_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v___x_1637_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1638_ = l_Nat_reprFast(v___x_1567_);
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
lean_dec_ref(v___x_1638_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1639_);
v___x_1641_ = v___x_1524_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_del_object(v___x_1524_);
goto v___jp_1569_;
}
}
else
{
lean_del_object(v___x_1524_);
goto v___jp_1569_;
}
v___jp_1569_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_array_fget_borrowed(v_val_1566_, v___x_1570_);
lean_inc(v___x_1571_);
v___x_1572_ = l_Lean_Json_getNat_x3f(v___x_1571_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_val_1566_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1581_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1572_);
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_array_fget_borrowed(v_val_1566_, v___x_1582_);
lean_inc(v___x_1583_);
v___x_1584_ = l_Lean_Json_getNat_x3f(v___x_1583_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1581_);
lean_dec(v_val_1566_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1593_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1584_);
v___x_1594_ = lean_unsigned_to_nat(2u);
v___x_1595_ = lean_array_fget_borrowed(v_val_1566_, v___x_1594_);
lean_inc(v___x_1595_);
v___x_1596_ = l_Lean_Json_getNat_x3f(v___x_1595_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_a_1593_);
lean_dec(v_a_1581_);
lean_dec(v_val_1566_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1605_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1596_);
v___x_1606_ = lean_unsigned_to_nat(3u);
v___x_1607_ = lean_array_fget_borrowed(v_val_1566_, v___x_1606_);
lean_inc(v___x_1607_);
v___x_1608_ = l_Lean_Json_getNat_x3f(v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1605_);
lean_dec(v_a_1593_);
lean_dec(v_a_1581_);
lean_dec(v_val_1566_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
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
lean_object* v_a_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1608_);
v___x_1618_ = lean_unsigned_to_nat(5u);
v___x_1619_ = lean_nat_dec_eq(v___x_1567_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_val_1566_);
v___x_1620_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1621_, 0, v_a_1581_);
lean_ctor_set(v___x_1621_, 1, v_a_1593_);
lean_ctor_set(v___x_1621_, 2, v_a_1605_);
lean_ctor_set(v___x_1621_, 3, v_a_1617_);
lean_ctor_set(v___x_1621_, 4, v___x_1620_);
v_a_1563_ = v___x_1621_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_array_fget(v_val_1566_, v___x_1568_);
lean_dec(v_val_1566_);
v___x_1623_ = l_Lean_Json_getStr_x3f(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1617_);
lean_dec(v_a_1605_);
lean_dec(v_a_1593_);
lean_dec(v_a_1581_);
lean_dec(v_a_1509_);
lean_dec(v_v_1489_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1623_);
v___x_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1581_);
lean_ctor_set(v___x_1633_, 1, v_a_1593_);
lean_ctor_set(v___x_1633_, 2, v_a_1605_);
lean_ctor_set(v___x_1633_, 3, v_a_1617_);
lean_ctor_set(v___x_1633_, 4, v_a_1632_);
v_a_1563_ = v___x_1633_;
goto v___jp_1562_;
}
}
}
}
}
}
}
}
v___jp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1530_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1489_, v___x_1526_, v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_definition_x3f_1528_);
lean_dec(v_a_1509_);
lean_dec(v_m_1487_);
lean_dec_ref(v_toLocation_1486_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; size_t v_sz_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1530_);
v_sz_1540_ = lean_array_size(v_a_1539_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1510_, v_toLocation_1486_, v_sz_1540_, v___x_1541_, v_a_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_definition_x3f_1528_);
lean_dec(v_a_1509_);
lean_dec(v_m_1487_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1561_; 
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1542_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_definition_x3f_1528_);
lean_ctor_set(v___x_1555_, 1, v_a_1551_);
v___x_1556_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1557_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1556_, v_a_1509_, v___x_1555_, v_m_1487_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1559_ = v___x_1553_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1563_);
v_definition_x3f_1528_ = v___x_1564_;
goto v___jp_1527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1644_, lean_object* v___f_1645_, lean_object* v_j_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Json_getObj_x3f(v_j_1646_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v___f_1645_);
lean_dec_ref(v___x_1644_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1647_);
v___x_1657_ = lean_box(1);
v___x_1658_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1644_, v___f_1645_, v___x_1657_, v_a_1656_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1665_, lean_object* v_k_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = l_Lean_Json_getObjValD(v_j_1665_, v_k_1666_);
v___x_1668_ = l_Lean_Json_getNat_x3f(v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1669_, lean_object* v_k_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1669_, v_k_1670_);
lean_dec_ref(v_k_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = l_Lean_Json_getObjValD(v_j_1672_, v_k_1673_);
v___x_1675_ = l_Lean_Json_getBool_x3f(v___x_1674_);
lean_dec(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1676_, v_k_1677_);
lean_dec_ref(v_k_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_bs_1683_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v_bs_1683_);
return v___x_1687_;
}
else
{
lean_object* v_v_1688_; 
v_v_1688_ = lean_array_uget_borrowed(v_bs_1683_, v_i_1682_);
if (lean_obj_tag(v_v_1688_) == 4)
{
lean_object* v_elems_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_elems_1689_ = lean_ctor_get(v_v_1688_, 0);
v___x_1690_ = lean_array_get_size(v_elems_1689_);
v___x_1691_ = lean_unsigned_to_nat(4u);
v___x_1692_ = lean_nat_dec_eq(v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v_bs_1683_);
goto v___jp_1684_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_array_fget_borrowed(v_elems_1689_, v___x_1693_);
lean_inc(v___x_1694_);
v___x_1695_ = l_Lean_Json_getStr_x3f(v___x_1694_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_bs_1683_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_a_1704_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1695_);
v___x_1705_ = lean_unsigned_to_nat(1u);
v___x_1706_ = lean_array_fget_borrowed(v_elems_1689_, v___x_1705_);
v___x_1707_ = l_Lean_Json_getBool_x3f(v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1704_);
lean_dec_ref(v_bs_1683_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1716_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1707_);
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = lean_array_fget_borrowed(v_elems_1689_, v___x_1717_);
v___x_1719_ = l_Lean_Json_getBool_x3f(v___x_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1716_);
lean_dec(v_a_1704_);
lean_dec_ref(v_bs_1683_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_a_1728_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1719_);
v___x_1729_ = lean_unsigned_to_nat(3u);
v___x_1730_ = lean_array_fget_borrowed(v_elems_1689_, v___x_1729_);
v___x_1731_ = l_Lean_Json_getBool_x3f(v___x_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1728_);
lean_dec(v_a_1716_);
lean_dec(v_a_1704_);
lean_dec_ref(v_bs_1683_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v_bs_x27_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1731_);
v_bs_x27_1741_ = lean_array_uset(v_bs_1683_, v_i_1682_, v___x_1693_);
v___x_1742_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1742_, 0, v_a_1704_);
v___x_1743_ = lean_unbox(v_a_1716_);
lean_dec(v_a_1716_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1, v___x_1743_);
v___x_1744_ = lean_unbox(v_a_1728_);
lean_dec(v_a_1728_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1 + 1, v___x_1744_);
v___x_1745_ = lean_unbox(v_a_1740_);
lean_dec(v_a_1740_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1 + 2, v___x_1745_);
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1682_, v___x_1746_);
v___x_1748_ = lean_array_uset(v_bs_x27_1741_, v_i_1682_, v___x_1742_);
v_i_1682_ = v___x_1747_;
v_bs_1683_ = v___x_1748_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1683_);
goto v___jp_1684_;
}
}
v___jp_1684_:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_bs_1752_){
_start:
{
size_t v_sz_boxed_1753_; size_t v_i_boxed_1754_; lean_object* v_res_1755_; 
v_sz_boxed_1753_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1753_, v_i_boxed_1754_, v_bs_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 4)
{
lean_object* v_elems_1759_; size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_elems_1759_ = lean_ctor_get(v_x_1758_, 0);
lean_inc_ref(v_elems_1759_);
lean_dec_ref(v_x_1758_);
v_sz_1760_ = lean_array_size(v_elems_1759_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1760_, v___x_1761_, v_elems_1759_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1763_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1764_ = lean_unsigned_to_nat(80u);
v___x_1765_ = l_Lean_Json_pretty(v_x_1758_, v___x_1764_);
v___x_1766_ = lean_string_append(v___x_1763_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1768_ = lean_string_append(v___x_1766_, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1770_, lean_object* v_k_1771_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l_Lean_Json_getObjValD(v_j_1770_, v_k_1771_);
v___x_1773_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1774_, lean_object* v_k_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1774_, v_k_1775_);
lean_dec_ref(v_k_1775_);
return v_res_1776_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = 1;
v___x_1786_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1790_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1791_ = lean_string_append(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = 1;
v___x_1795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1798_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1799_ = lean_string_append(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1803_ = lean_string_append(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = 1;
v___x_1808_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1811_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1812_ = lean_string_append(v___x_1811_, v___x_1810_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1815_ = lean_string_append(v___x_1814_, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = 1;
v___x_1820_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1821_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1823_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1824_ = lean_string_append(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1827_ = lean_string_append(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1828_);
v___x_1830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1828_, v___x_1829_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_json_1828_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1836_ = lean_string_append(v___x_1835_, v_a_1831_);
lean_dec(v_a_1831_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_json_1828_);
v_a_1841_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1830_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1830_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 0);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
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
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1830_);
v___x_1850_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1828_);
v___x_1851_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1828_, v___x_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1849_);
lean_dec(v_json_1828_);
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1857_ = lean_string_append(v___x_1856_, v_a_1852_);
lean_dec(v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1849_);
lean_dec(v_json_1828_);
v_a_1862_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1851_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1851_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
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
lean_object* v_a_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_a_1870_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1851_);
v___x_1871_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1872_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1828_, v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1870_);
lean_dec(v_a_1849_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1878_ = lean_string_append(v___x_1877_, v_a_1873_);
lean_dec(v_a_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1878_);
v___x_1880_ = v___x_1875_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_a_1870_);
lean_dec(v_a_1849_);
v_a_1883_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1872_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1872_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 0);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
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
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1900_; 
v_a_1891_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1893_ = v___x_1872_;
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1872_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___x_1898_; 
v___x_1895_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1895_, 0, v_a_1849_);
lean_ctor_set(v___x_1895_, 1, v_a_1891_);
v___x_1896_ = lean_unbox(v_a_1870_);
lean_dec(v_a_1870_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*2, v___x_1896_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1895_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1903_, size_t v_i_1904_, lean_object* v_bs_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_lt(v_i_1904_, v_sz_1903_);
if (v___x_1906_ == 0)
{
return v_bs_1905_;
}
else
{
lean_object* v_v_1907_; lean_object* v_module_1908_; uint8_t v_isPrivate_1909_; uint8_t v_isAll_1910_; uint8_t v_isMeta_1911_; lean_object* v___x_1912_; lean_object* v_bs_x27_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v_v_1907_ = lean_array_uget_borrowed(v_bs_1905_, v_i_1904_);
v_module_1908_ = lean_ctor_get(v_v_1907_, 0);
lean_inc_ref(v_module_1908_);
v_isPrivate_1909_ = lean_ctor_get_uint8(v_v_1907_, sizeof(void*)*1);
v_isAll_1910_ = lean_ctor_get_uint8(v_v_1907_, sizeof(void*)*1 + 1);
v_isMeta_1911_ = lean_ctor_get_uint8(v_v_1907_, sizeof(void*)*1 + 2);
v___x_1912_ = lean_unsigned_to_nat(0u);
v_bs_x27_1913_ = lean_array_uset(v_bs_1905_, v_i_1904_, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_module_1908_);
v___x_1915_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1915_, 0, v_isPrivate_1909_);
v___x_1916_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1916_, 0, v_isAll_1910_);
v___x_1917_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1917_, 0, v_isMeta_1911_);
v___x_1918_ = lean_unsigned_to_nat(4u);
v___x_1919_ = lean_mk_empty_array_with_capacity(v___x_1918_);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1914_);
v___x_1921_ = lean_array_push(v___x_1920_, v___x_1915_);
v___x_1922_ = lean_array_push(v___x_1921_, v___x_1916_);
v___x_1923_ = lean_array_push(v___x_1922_, v___x_1917_);
v___x_1924_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1904_, v___x_1925_);
v___x_1927_ = lean_array_uset(v_bs_x27_1913_, v_i_1904_, v___x_1924_);
v_i_1904_ = v___x_1926_;
v_bs_1905_ = v___x_1927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1929_, lean_object* v_i_1930_, lean_object* v_bs_1931_){
_start:
{
size_t v_sz_boxed_1932_; size_t v_i_boxed_1933_; lean_object* v_res_1934_; 
v_sz_boxed_1932_ = lean_unbox_usize(v_sz_1929_);
lean_dec(v_sz_1929_);
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_res_1934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1932_, v_i_boxed_1933_, v_bs_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1935_){
_start:
{
size_t v_sz_1936_; size_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_sz_1936_ = lean_array_size(v_a_1935_);
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1936_, v___x_1937_, v_a_1935_);
v___x_1939_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
if (lean_obj_tag(v_a_1940_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_array_to_list(v_a_1941_);
return v___x_1942_;
}
else
{
lean_object* v_head_1943_; lean_object* v_tail_1944_; lean_object* v___x_1945_; 
v_head_1943_ = lean_ctor_get(v_a_1940_, 0);
lean_inc(v_head_1943_);
v_tail_1944_ = lean_ctor_get(v_a_1940_, 1);
lean_inc(v_tail_1944_);
lean_dec_ref(v_a_1940_);
v___x_1945_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1941_, v_head_1943_);
v_a_1940_ = v_tail_1944_;
v_a_1941_ = v___x_1945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1949_){
_start:
{
lean_object* v_version_1950_; uint8_t v_isSetupFailure_1951_; lean_object* v_directImports_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_version_1950_ = lean_ctor_get(v_x_1949_, 0);
lean_inc(v_version_1950_);
v_isSetupFailure_1951_ = lean_ctor_get_uint8(v_x_1949_, sizeof(void*)*2);
v_directImports_1952_ = lean_ctor_get(v_x_1949_, 1);
lean_inc_ref(v_directImports_1952_);
lean_dec_ref(v_x_1949_);
v___x_1953_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1954_ = l_Lean_JsonNumber_fromNat(v_version_1950_);
v___x_1955_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1953_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1960_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1960_, 0, v_isSetupFailure_1951_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___x_1957_);
v___x_1963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1964_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1952_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1957_);
v___x_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v___x_1957_);
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1962_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1958_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1971_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1969_, v___x_1970_);
v___x_1972_ = l_Lean_Json_mkObj(v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1975_, lean_object* v_v_1976_, lean_object* v_t_1977_){
_start:
{
if (lean_obj_tag(v_t_1977_) == 0)
{
lean_object* v_size_1978_; lean_object* v_k_1979_; lean_object* v_v_1980_; lean_object* v_l_1981_; lean_object* v_r_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2263_; 
v_size_1978_ = lean_ctor_get(v_t_1977_, 0);
v_k_1979_ = lean_ctor_get(v_t_1977_, 1);
v_v_1980_ = lean_ctor_get(v_t_1977_, 2);
v_l_1981_ = lean_ctor_get(v_t_1977_, 3);
v_r_1982_ = lean_ctor_get(v_t_1977_, 4);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_t_1977_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_1984_ = v_t_1977_;
v_isShared_1985_ = v_isSharedCheck_2263_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_r_1982_);
lean_inc(v_l_1981_);
lean_inc(v_v_1980_);
lean_inc(v_k_1979_);
lean_inc(v_size_1978_);
lean_dec(v_t_1977_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2263_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_string_dec_lt(v_k_1975_, v_k_1979_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_string_dec_eq(v_k_1975_, v_k_1979_);
if (v___x_1987_ == 0)
{
lean_object* v_impl_1988_; lean_object* v___x_1989_; 
lean_dec(v_size_1978_);
v_impl_1988_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1975_, v_v_1976_, v_r_1982_);
v___x_1989_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1981_) == 0)
{
lean_object* v_size_1990_; lean_object* v_size_1991_; lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v_l_1994_; lean_object* v_r_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_size_1990_ = lean_ctor_get(v_l_1981_, 0);
v_size_1991_ = lean_ctor_get(v_impl_1988_, 0);
lean_inc(v_size_1991_);
v_k_1992_ = lean_ctor_get(v_impl_1988_, 1);
lean_inc(v_k_1992_);
v_v_1993_ = lean_ctor_get(v_impl_1988_, 2);
lean_inc(v_v_1993_);
v_l_1994_ = lean_ctor_get(v_impl_1988_, 3);
lean_inc(v_l_1994_);
v_r_1995_ = lean_ctor_get(v_impl_1988_, 4);
lean_inc(v_r_1995_);
v___x_1996_ = lean_unsigned_to_nat(3u);
v___x_1997_ = lean_nat_mul(v___x_1996_, v_size_1990_);
v___x_1998_ = lean_nat_dec_lt(v___x_1997_, v_size_1991_);
lean_dec(v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec(v_r_1995_);
lean_dec(v_l_1994_);
lean_dec(v_v_1993_);
lean_dec(v_k_1992_);
v___x_1999_ = lean_nat_add(v___x_1989_, v_size_1990_);
v___x_2000_ = lean_nat_add(v___x_1999_, v_size_1991_);
lean_dec(v_size_1991_);
lean_dec(v___x_1999_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_impl_1988_);
lean_ctor_set(v___x_1984_, 0, v___x_2000_);
v___x_2002_ = v___x_1984_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_impl_1988_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
else
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2067_; 
v_isSharedCheck_2067_ = !lean_is_exclusive(v_impl_1988_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2068_ = lean_ctor_get(v_impl_1988_, 4);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_impl_1988_, 3);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_impl_1988_, 2);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_impl_1988_, 1);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_impl_1988_, 0);
lean_dec(v_unused_2072_);
v___x_2005_ = v_impl_1988_;
v_isShared_2006_ = v_isSharedCheck_2067_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v_impl_1988_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2067_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_size_2007_; lean_object* v_k_2008_; lean_object* v_v_2009_; lean_object* v_l_2010_; lean_object* v_r_2011_; lean_object* v_size_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_size_2007_ = lean_ctor_get(v_l_1994_, 0);
v_k_2008_ = lean_ctor_get(v_l_1994_, 1);
v_v_2009_ = lean_ctor_get(v_l_1994_, 2);
v_l_2010_ = lean_ctor_get(v_l_1994_, 3);
v_r_2011_ = lean_ctor_get(v_l_1994_, 4);
v_size_2012_ = lean_ctor_get(v_r_1995_, 0);
v___x_2013_ = lean_unsigned_to_nat(2u);
v___x_2014_ = lean_nat_mul(v___x_2013_, v_size_2012_);
v___x_2015_ = lean_nat_dec_lt(v_size_2007_, v___x_2014_);
lean_dec(v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2043_; 
lean_inc(v_r_2011_);
lean_inc(v_l_2010_);
lean_inc(v_v_2009_);
lean_inc(v_k_2008_);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2044_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2048_);
v___x_2017_ = v_l_1994_;
v_isShared_2018_ = v_isSharedCheck_2043_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_l_1994_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2043_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2033_; 
v___x_2019_ = lean_nat_add(v___x_1989_, v_size_1990_);
v___x_2020_ = lean_nat_add(v___x_2019_, v_size_1991_);
lean_dec(v_size_1991_);
if (lean_obj_tag(v_l_2010_) == 0)
{
lean_object* v_size_2041_; 
v_size_2041_ = lean_ctor_get(v_l_2010_, 0);
lean_inc(v_size_2041_);
v___y_2033_ = v_size_2041_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v___y_2033_ = v___x_2042_;
goto v___jp_2032_;
}
v___jp_2021_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_nat_add(v___y_2022_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec(v___y_2022_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 4, v_r_1995_);
lean_ctor_set(v___x_2017_, 3, v_r_2011_);
lean_ctor_set(v___x_2017_, 2, v_v_1993_);
lean_ctor_set(v___x_2017_, 1, v_k_1992_);
lean_ctor_set(v___x_2017_, 0, v___x_2025_);
v___x_2027_ = v___x_2017_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_r_2011_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_r_1995_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 4, v___x_2027_);
lean_ctor_set(v___x_2005_, 3, v___y_2023_);
lean_ctor_set(v___x_2005_, 2, v_v_2009_);
lean_ctor_set(v___x_2005_, 1, v_k_2008_);
lean_ctor_set(v___x_2005_, 0, v___x_2020_);
v___x_2029_ = v___x_2005_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_k_2008_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_v_2009_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v___y_2023_);
lean_ctor_set(v_reuseFailAlloc_2030_, 4, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2034_ = lean_nat_add(v___x_2019_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec(v___x_2019_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_l_2010_);
lean_ctor_set(v___x_1984_, 0, v___x_2034_);
v___x_2036_ = v___x_1984_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_l_2010_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_nat_add(v___x_1989_, v_size_2012_);
if (lean_obj_tag(v_r_2011_) == 0)
{
lean_object* v_size_2038_; 
v_size_2038_ = lean_ctor_get(v_r_2011_, 0);
lean_inc(v_size_2038_);
v___y_2022_ = v___x_2037_;
v___y_2023_ = v___x_2036_;
v___y_2024_ = v_size_2038_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___y_2022_ = v___x_2037_;
v___y_2023_ = v___x_2036_;
v___y_2024_ = v___x_2039_;
goto v___jp_2021_;
}
}
}
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_del_object(v___x_1984_);
v___x_2049_ = lean_nat_add(v___x_1989_, v_size_1990_);
v___x_2050_ = lean_nat_add(v___x_2049_, v_size_1991_);
lean_dec(v_size_1991_);
v___x_2051_ = lean_nat_add(v___x_2049_, v_size_2007_);
lean_dec(v___x_2049_);
lean_inc_ref(v_l_1981_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 4, v_l_1994_);
lean_ctor_set(v___x_2005_, 3, v_l_1981_);
lean_ctor_set(v___x_2005_, 2, v_v_1980_);
lean_ctor_set(v___x_2005_, 1, v_k_1979_);
lean_ctor_set(v___x_2005_, 0, v___x_2051_);
v___x_2053_ = v___x_2005_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_l_1994_);
v___x_2053_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_isSharedCheck_2060_ = !lean_is_exclusive(v_l_1981_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; lean_object* v_unused_2062_; lean_object* v_unused_2063_; lean_object* v_unused_2064_; lean_object* v_unused_2065_; 
v_unused_2061_ = lean_ctor_get(v_l_1981_, 4);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_l_1981_, 3);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_l_1981_, 2);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v_l_1981_, 1);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_l_1981_, 0);
lean_dec(v_unused_2065_);
v___x_2055_ = v_l_1981_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_l_1981_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v_r_1995_);
lean_ctor_set(v___x_2055_, 3, v___x_2053_);
lean_ctor_set(v___x_2055_, 2, v_v_1993_);
lean_ctor_set(v___x_2055_, 1, v_k_1992_);
lean_ctor_set(v___x_2055_, 0, v___x_2050_);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_r_1995_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2073_; 
v_l_2073_ = lean_ctor_get(v_impl_1988_, 3);
lean_inc(v_l_2073_);
if (lean_obj_tag(v_l_2073_) == 0)
{
lean_object* v_r_2074_; lean_object* v_k_2075_; lean_object* v_v_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2099_; 
v_r_2074_ = lean_ctor_get(v_impl_1988_, 4);
v_k_2075_ = lean_ctor_get(v_impl_1988_, 1);
v_v_2076_ = lean_ctor_get(v_impl_1988_, 2);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_impl_1988_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; lean_object* v_unused_2101_; 
v_unused_2100_ = lean_ctor_get(v_impl_1988_, 3);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_impl_1988_, 0);
lean_dec(v_unused_2101_);
v___x_2078_ = v_impl_1988_;
v_isShared_2079_ = v_isSharedCheck_2099_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_r_2074_);
lean_inc(v_v_2076_);
lean_inc(v_k_2075_);
lean_dec(v_impl_1988_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2099_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_k_2080_; lean_object* v_v_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2095_; 
v_k_2080_ = lean_ctor_get(v_l_2073_, 1);
v_v_2081_ = lean_ctor_get(v_l_2073_, 2);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_l_2073_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; 
v_unused_2096_ = lean_ctor_get(v_l_2073_, 4);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_l_2073_, 3);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_l_2073_, 0);
lean_dec(v_unused_2098_);
v___x_2083_ = v_l_2073_;
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_v_2081_);
lean_inc(v_k_2080_);
lean_dec(v_l_2073_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2095_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2074_, 2);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 4, v_r_2074_);
lean_ctor_set(v___x_2083_, 3, v_r_2074_);
lean_ctor_set(v___x_2083_, 2, v_v_1980_);
lean_ctor_set(v___x_2083_, 1, v_k_1979_);
lean_ctor_set(v___x_2083_, 0, v___x_1989_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_r_2074_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v_r_2074_);
v___x_2087_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
lean_inc(v_r_2074_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 3, v_r_2074_);
lean_ctor_set(v___x_2078_, 0, v___x_1989_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_k_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_v_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_r_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_r_2074_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v___x_2089_);
lean_ctor_set(v___x_1984_, 3, v___x_2087_);
lean_ctor_set(v___x_1984_, 2, v_v_2081_);
lean_ctor_set(v___x_1984_, 1, v_k_2080_);
lean_ctor_set(v___x_1984_, 0, v___x_2085_);
v___x_2091_ = v___x_1984_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_2080_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_2081_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
else
{
lean_object* v_r_2102_; 
v_r_2102_ = lean_ctor_get(v_impl_1988_, 4);
lean_inc(v_r_2102_);
if (lean_obj_tag(v_r_2102_) == 0)
{
lean_object* v_k_2103_; lean_object* v_v_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2115_; 
v_k_2103_ = lean_ctor_get(v_impl_1988_, 1);
v_v_2104_ = lean_ctor_get(v_impl_1988_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_impl_1988_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; 
v_unused_2116_ = lean_ctor_get(v_impl_1988_, 4);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_1988_, 3);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_impl_1988_, 0);
lean_dec(v_unused_2118_);
v___x_2106_ = v_impl_1988_;
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_v_2104_);
lean_inc(v_k_2103_);
lean_dec(v_impl_1988_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_unsigned_to_nat(3u);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 4, v_l_2073_);
lean_ctor_set(v___x_2106_, 2, v_v_1980_);
lean_ctor_set(v___x_2106_, 1, v_k_1979_);
lean_ctor_set(v___x_2106_, 0, v___x_1989_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_l_2073_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_l_2073_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_r_2102_);
lean_ctor_set(v___x_1984_, 3, v___x_2110_);
lean_ctor_set(v___x_1984_, 2, v_v_2104_);
lean_ctor_set(v___x_1984_, 1, v_k_2103_);
lean_ctor_set(v___x_1984_, 0, v___x_2108_);
v___x_2112_ = v___x_1984_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2103_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2104_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_r_2102_);
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
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_unsigned_to_nat(2u);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_impl_1988_);
lean_ctor_set(v___x_1984_, 3, v_r_2102_);
lean_ctor_set(v___x_1984_, 0, v___x_2119_);
v___x_2121_ = v___x_1984_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_r_2102_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_impl_1988_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
else
{
lean_object* v___x_2124_; 
lean_dec(v_v_1980_);
lean_dec(v_k_1979_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 2, v_v_1976_);
lean_ctor_set(v___x_1984_, 1, v_k_1975_);
v___x_2124_ = v___x_1984_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_size_1978_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_r_1982_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
else
{
lean_object* v_impl_2126_; lean_object* v___x_2127_; 
lean_dec(v_size_1978_);
v_impl_2126_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1975_, v_v_1976_, v_l_1981_);
v___x_2127_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1982_) == 0)
{
lean_object* v_size_2128_; lean_object* v_size_2129_; lean_object* v_k_2130_; lean_object* v_v_2131_; lean_object* v_l_2132_; lean_object* v_r_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_size_2128_ = lean_ctor_get(v_r_1982_, 0);
v_size_2129_ = lean_ctor_get(v_impl_2126_, 0);
lean_inc(v_size_2129_);
v_k_2130_ = lean_ctor_get(v_impl_2126_, 1);
lean_inc(v_k_2130_);
v_v_2131_ = lean_ctor_get(v_impl_2126_, 2);
lean_inc(v_v_2131_);
v_l_2132_ = lean_ctor_get(v_impl_2126_, 3);
lean_inc(v_l_2132_);
v_r_2133_ = lean_ctor_get(v_impl_2126_, 4);
lean_inc(v_r_2133_);
v___x_2134_ = lean_unsigned_to_nat(3u);
v___x_2135_ = lean_nat_mul(v___x_2134_, v_size_2128_);
v___x_2136_ = lean_nat_dec_lt(v___x_2135_, v_size_2129_);
lean_dec(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
lean_dec(v_r_2133_);
lean_dec(v_l_2132_);
lean_dec(v_v_2131_);
lean_dec(v_k_2130_);
v___x_2137_ = lean_nat_add(v___x_2127_, v_size_2129_);
lean_dec(v_size_2129_);
v___x_2138_ = lean_nat_add(v___x_2137_, v_size_2128_);
lean_dec(v___x_2137_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 3, v_impl_2126_);
lean_ctor_set(v___x_1984_, 0, v___x_2138_);
v___x_2140_ = v___x_1984_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_impl_2126_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_r_1982_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
else
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2207_; 
v_isSharedCheck_2207_ = !lean_is_exclusive(v_impl_2126_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; 
v_unused_2208_ = lean_ctor_get(v_impl_2126_, 4);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_impl_2126_, 3);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_impl_2126_, 2);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_impl_2126_, 1);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_impl_2126_, 0);
lean_dec(v_unused_2212_);
v___x_2143_ = v_impl_2126_;
v_isShared_2144_ = v_isSharedCheck_2207_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v_impl_2126_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2207_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_size_2145_; lean_object* v_size_2146_; lean_object* v_k_2147_; lean_object* v_v_2148_; lean_object* v_l_2149_; lean_object* v_r_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_size_2145_ = lean_ctor_get(v_l_2132_, 0);
v_size_2146_ = lean_ctor_get(v_r_2133_, 0);
v_k_2147_ = lean_ctor_get(v_r_2133_, 1);
v_v_2148_ = lean_ctor_get(v_r_2133_, 2);
v_l_2149_ = lean_ctor_get(v_r_2133_, 3);
v_r_2150_ = lean_ctor_get(v_r_2133_, 4);
v___x_2151_ = lean_unsigned_to_nat(2u);
v___x_2152_ = lean_nat_mul(v___x_2151_, v_size_2145_);
v___x_2153_ = lean_nat_dec_lt(v_size_2146_, v___x_2152_);
lean_dec(v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2182_; 
lean_inc(v_r_2150_);
lean_inc(v_l_2149_);
lean_inc(v_v_2148_);
lean_inc(v_k_2147_);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_r_2133_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2183_ = lean_ctor_get(v_r_2133_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_r_2133_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_r_2133_, 2);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_r_2133_, 1);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_r_2133_, 0);
lean_dec(v_unused_2187_);
v___x_2155_ = v_r_2133_;
v_isShared_2156_ = v_isSharedCheck_2182_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_r_2133_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2182_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___x_2170_; lean_object* v___y_2172_; 
v___x_2157_ = lean_nat_add(v___x_2127_, v_size_2129_);
lean_dec(v_size_2129_);
v___x_2158_ = lean_nat_add(v___x_2157_, v_size_2128_);
lean_dec(v___x_2157_);
v___x_2170_ = lean_nat_add(v___x_2127_, v_size_2145_);
if (lean_obj_tag(v_l_2149_) == 0)
{
lean_object* v_size_2180_; 
v_size_2180_ = lean_ctor_get(v_l_2149_, 0);
lean_inc(v_size_2180_);
v___y_2172_ = v_size_2180_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___y_2172_ = v___x_2181_;
goto v___jp_2171_;
}
v___jp_2159_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_nat_add(v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec(v___y_2161_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 4, v_r_1982_);
lean_ctor_set(v___x_2155_, 3, v_r_2150_);
lean_ctor_set(v___x_2155_, 2, v_v_1980_);
lean_ctor_set(v___x_2155_, 1, v_k_1979_);
lean_ctor_set(v___x_2155_, 0, v___x_2163_);
v___x_2165_ = v___x_2155_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_r_2150_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_r_1982_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v___x_2165_);
lean_ctor_set(v___x_2143_, 3, v___y_2160_);
lean_ctor_set(v___x_2143_, 2, v_v_2148_);
lean_ctor_set(v___x_2143_, 1, v_k_2147_);
lean_ctor_set(v___x_2143_, 0, v___x_2158_);
v___x_2167_ = v___x_2143_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_2147_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_2148_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v___y_2160_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
v___jp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_nat_add(v___x_2170_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec(v___x_2170_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_l_2149_);
lean_ctor_set(v___x_1984_, 3, v_l_2132_);
lean_ctor_set(v___x_1984_, 2, v_v_2131_);
lean_ctor_set(v___x_1984_, 1, v_k_2130_);
lean_ctor_set(v___x_1984_, 0, v___x_2173_);
v___x_2175_ = v___x_1984_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_k_2130_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_v_2131_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_l_2132_);
lean_ctor_set(v_reuseFailAlloc_2179_, 4, v_l_2149_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_nat_add(v___x_2127_, v_size_2128_);
if (lean_obj_tag(v_r_2150_) == 0)
{
lean_object* v_size_2177_; 
v_size_2177_ = lean_ctor_get(v_r_2150_, 0);
lean_inc(v_size_2177_);
v___y_2160_ = v___x_2175_;
v___y_2161_ = v___x_2176_;
v___y_2162_ = v_size_2177_;
goto v___jp_2159_;
}
else
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___y_2160_ = v___x_2175_;
v___y_2161_ = v___x_2176_;
v___y_2162_ = v___x_2178_;
goto v___jp_2159_;
}
}
}
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_del_object(v___x_1984_);
v___x_2188_ = lean_nat_add(v___x_2127_, v_size_2129_);
lean_dec(v_size_2129_);
v___x_2189_ = lean_nat_add(v___x_2188_, v_size_2128_);
lean_dec(v___x_2188_);
v___x_2190_ = lean_nat_add(v___x_2127_, v_size_2128_);
v___x_2191_ = lean_nat_add(v___x_2190_, v_size_2146_);
lean_dec(v___x_2190_);
lean_inc_ref(v_r_1982_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v_r_1982_);
lean_ctor_set(v___x_2143_, 3, v_r_2133_);
lean_ctor_set(v___x_2143_, 2, v_v_1980_);
lean_ctor_set(v___x_2143_, 1, v_k_1979_);
lean_ctor_set(v___x_2143_, 0, v___x_2191_);
v___x_2193_ = v___x_2143_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_r_2133_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_r_1982_);
v___x_2193_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
v_isSharedCheck_2200_ = !lean_is_exclusive(v_r_1982_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; lean_object* v_unused_2204_; lean_object* v_unused_2205_; 
v_unused_2201_ = lean_ctor_get(v_r_1982_, 4);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_r_1982_, 3);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_r_1982_, 2);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_r_1982_, 1);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_r_1982_, 0);
lean_dec(v_unused_2205_);
v___x_2195_ = v_r_1982_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v_r_1982_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v___x_2193_);
lean_ctor_set(v___x_2195_, 3, v_l_2132_);
lean_ctor_set(v___x_2195_, 2, v_v_2131_);
lean_ctor_set(v___x_2195_, 1, v_k_2130_);
lean_ctor_set(v___x_2195_, 0, v___x_2189_);
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2130_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2131_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_l_2132_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v___x_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2213_; 
v_l_2213_ = lean_ctor_get(v_impl_2126_, 3);
lean_inc(v_l_2213_);
if (lean_obj_tag(v_l_2213_) == 0)
{
lean_object* v_r_2214_; lean_object* v_k_2215_; lean_object* v_v_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2227_; 
v_r_2214_ = lean_ctor_get(v_impl_2126_, 4);
v_k_2215_ = lean_ctor_get(v_impl_2126_, 1);
v_v_2216_ = lean_ctor_get(v_impl_2126_, 2);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_impl_2126_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2228_ = lean_ctor_get(v_impl_2126_, 3);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_impl_2126_, 0);
lean_dec(v_unused_2229_);
v___x_2218_ = v_impl_2126_;
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_r_2214_);
lean_inc(v_v_2216_);
lean_inc(v_k_2215_);
lean_dec(v_impl_2126_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2214_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 3, v_r_2214_);
lean_ctor_set(v___x_2218_, 2, v_v_1980_);
lean_ctor_set(v___x_2218_, 1, v_k_1979_);
lean_ctor_set(v___x_2218_, 0, v___x_2127_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_r_2214_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_r_2214_);
v___x_2222_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v___x_2222_);
lean_ctor_set(v___x_1984_, 3, v_l_2213_);
lean_ctor_set(v___x_1984_, 2, v_v_2216_);
lean_ctor_set(v___x_1984_, 1, v_k_2215_);
lean_ctor_set(v___x_1984_, 0, v___x_2220_);
v___x_2224_ = v___x_1984_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2215_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2216_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_l_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v_r_2230_; 
v_r_2230_ = lean_ctor_get(v_impl_2126_, 4);
lean_inc(v_r_2230_);
if (lean_obj_tag(v_r_2230_) == 0)
{
lean_object* v_k_2231_; lean_object* v_v_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2255_; 
v_k_2231_ = lean_ctor_get(v_impl_2126_, 1);
v_v_2232_ = lean_ctor_get(v_impl_2126_, 2);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_impl_2126_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; 
v_unused_2256_ = lean_ctor_get(v_impl_2126_, 4);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_impl_2126_, 3);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_impl_2126_, 0);
lean_dec(v_unused_2258_);
v___x_2234_ = v_impl_2126_;
v_isShared_2235_ = v_isSharedCheck_2255_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_v_2232_);
lean_inc(v_k_2231_);
lean_dec(v_impl_2126_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2255_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_k_2236_; lean_object* v_v_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2251_; 
v_k_2236_ = lean_ctor_get(v_r_2230_, 1);
v_v_2237_ = lean_ctor_get(v_r_2230_, 2);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_r_2230_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; 
v_unused_2252_ = lean_ctor_get(v_r_2230_, 4);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_r_2230_, 3);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_r_2230_, 0);
lean_dec(v_unused_2254_);
v___x_2239_ = v_r_2230_;
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_v_2237_);
lean_inc(v_k_2236_);
lean_dec(v_r_2230_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(3u);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 4, v_l_2213_);
lean_ctor_set(v___x_2239_, 3, v_l_2213_);
lean_ctor_set(v___x_2239_, 2, v_v_2232_);
lean_ctor_set(v___x_2239_, 1, v_k_2231_);
lean_ctor_set(v___x_2239_, 0, v___x_2127_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_k_2231_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_v_2232_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v_l_2213_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v_l_2213_);
v___x_2243_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 4, v_l_2213_);
lean_ctor_set(v___x_2234_, 2, v_v_1980_);
lean_ctor_set(v___x_2234_, 1, v_k_1979_);
lean_ctor_set(v___x_2234_, 0, v___x_2127_);
v___x_2245_ = v___x_2234_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_l_2213_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_l_2213_);
v___x_2245_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v___x_2245_);
lean_ctor_set(v___x_1984_, 3, v___x_2243_);
lean_ctor_set(v___x_1984_, 2, v_v_2237_);
lean_ctor_set(v___x_1984_, 1, v_k_2236_);
lean_ctor_set(v___x_1984_, 0, v___x_2241_);
v___x_2247_ = v___x_1984_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_k_2236_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_v_2237_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v___x_2245_);
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
else
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_unsigned_to_nat(2u);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 4, v_r_2230_);
lean_ctor_set(v___x_1984_, 3, v_impl_2126_);
lean_ctor_set(v___x_1984_, 0, v___x_2259_);
v___x_2261_ = v___x_1984_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_k_1979_);
lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_v_1980_);
lean_ctor_set(v_reuseFailAlloc_2262_, 3, v_impl_2126_);
lean_ctor_set(v_reuseFailAlloc_2262_, 4, v_r_2230_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_k_1975_);
lean_ctor_set(v___x_2265_, 2, v_v_1976_);
lean_ctor_set(v___x_2265_, 3, v_t_1977_);
lean_ctor_set(v___x_2265_, 4, v_t_1977_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2267_) == 0)
{
lean_object* v_k_2268_; lean_object* v_v_2269_; lean_object* v_l_2270_; lean_object* v_r_2271_; lean_object* v___x_2272_; 
v_k_2268_ = lean_ctor_get(v_x_2267_, 1);
lean_inc(v_k_2268_);
v_v_2269_ = lean_ctor_get(v_x_2267_, 2);
lean_inc(v_v_2269_);
v_l_2270_ = lean_ctor_get(v_x_2267_, 3);
lean_inc(v_l_2270_);
v_r_2271_ = lean_ctor_get(v_x_2267_, 4);
lean_inc(v_r_2271_);
lean_dec_ref(v_x_2267_);
v___x_2272_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2266_, v_l_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec(v_r_2271_);
lean_dec(v_v_2269_);
lean_dec(v_k_2268_);
return v___x_2272_;
}
else
{
if (lean_obj_tag(v_v_2269_) == 4)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2387_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2387_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2387_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v_elems_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_elems_2277_ = lean_ctor_get(v_v_2269_, 0);
lean_inc_ref(v_elems_2277_);
lean_dec_ref(v_v_2269_);
v___x_2278_ = lean_array_get_size(v_elems_2277_);
v___x_2279_ = lean_unsigned_to_nat(8u);
v___x_2280_ = lean_nat_dec_eq(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v___x_2281_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2282_ = l_Nat_reprFast(v___x_2278_);
v___x_2283_ = lean_string_append(v___x_2281_, v___x_2282_);
lean_dec_ref(v___x_2282_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2283_);
v___x_2285_ = v___x_2275_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_del_object(v___x_2275_);
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2288_);
lean_inc(v___x_2289_);
v___x_2290_ = l_Lean_Json_getNat_x3f(v___x_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_a_2299_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2290_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2300_);
lean_inc(v___x_2301_);
v___x_2302_ = l_Lean_Json_getNat_x3f(v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_a_2311_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2302_);
v___x_2312_ = lean_unsigned_to_nat(2u);
v___x_2313_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2312_);
lean_inc(v___x_2313_);
v___x_2314_ = l_Lean_Json_getNat_x3f(v___x_2313_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2323_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2314_);
v___x_2324_ = lean_unsigned_to_nat(3u);
v___x_2325_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2324_);
lean_inc(v___x_2325_);
v___x_2326_ = l_Lean_Json_getNat_x3f(v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_a_2323_);
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2335_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2326_);
v___x_2336_ = lean_unsigned_to_nat(4u);
v___x_2337_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2336_);
lean_inc(v___x_2337_);
v___x_2338_ = l_Lean_Json_getNat_x3f(v___x_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_2335_);
lean_dec(v_a_2323_);
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_a_2347_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2338_);
v___x_2348_ = lean_unsigned_to_nat(5u);
v___x_2349_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2348_);
lean_inc(v___x_2349_);
v___x_2350_ = l_Lean_Json_getNat_x3f(v___x_2349_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_a_2347_);
lean_dec(v_a_2335_);
lean_dec(v_a_2323_);
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
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
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2359_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2350_);
v___x_2360_ = lean_unsigned_to_nat(6u);
v___x_2361_ = lean_array_get_borrowed(v___x_2287_, v_elems_2277_, v___x_2360_);
lean_inc(v___x_2361_);
v___x_2362_ = l_Lean_Json_getNat_x3f(v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_a_2359_);
lean_dec(v_a_2347_);
lean_dec(v_a_2335_);
lean_dec(v_a_2323_);
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec_ref(v_elems_2277_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2371_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2362_);
v___x_2372_ = lean_unsigned_to_nat(7u);
v___x_2373_ = lean_array_get(v___x_2287_, v_elems_2277_, v___x_2372_);
lean_dec_ref(v_elems_2277_);
v___x_2374_ = l_Lean_Json_getNat_x3f(v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2371_);
lean_dec(v_a_2359_);
lean_dec(v_a_2347_);
lean_dec(v_a_2335_);
lean_dec(v_a_2323_);
lean_dec(v_a_2311_);
lean_dec(v_a_2299_);
lean_dec(v_a_2273_);
lean_dec(v_r_2271_);
lean_dec(v_k_2268_);
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
lean_dec_ref(v___x_2374_);
v___x_2384_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2384_, 0, v_a_2299_);
lean_ctor_set(v___x_2384_, 1, v_a_2311_);
lean_ctor_set(v___x_2384_, 2, v_a_2323_);
lean_ctor_set(v___x_2384_, 3, v_a_2335_);
lean_ctor_set(v___x_2384_, 4, v_a_2347_);
lean_ctor_set(v___x_2384_, 5, v_a_2359_);
lean_ctor_set(v___x_2384_, 6, v_a_2371_);
lean_ctor_set(v___x_2384_, 7, v_a_2383_);
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2268_, v___x_2384_, v_a_2273_);
v_init_2266_ = v___x_2385_;
v_x_2267_ = v_r_2271_;
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
lean_object* v___x_2388_; 
lean_dec_ref(v___x_2272_);
lean_dec(v_r_2271_);
lean_dec(v_v_2269_);
lean_dec(v_k_2268_);
v___x_2388_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
return v___x_2388_;
}
}
}
else
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_init_2266_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2390_, lean_object* v_k_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = l_Lean_Json_getObjValD(v_j_2390_, v_k_2391_);
v___x_2393_ = l_Lean_Json_getObj_x3f(v___x_2392_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_a_2402_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2393_);
v___x_2403_ = lean_box(1);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2403_, v_a_2402_);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2405_, lean_object* v_k_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2405_, v_k_2406_);
lean_dec_ref(v_k_2406_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2408_, size_t v_i_2409_, lean_object* v_bs_2410_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_usize_dec_lt(v_i_2409_, v_sz_2408_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_bs_2410_);
return v___x_2412_;
}
else
{
lean_object* v_v_2413_; lean_object* v___x_2414_; lean_object* v_bs_x27_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v_v_2413_ = lean_array_uget(v_bs_2410_, v_i_2409_);
v___x_2414_ = lean_unsigned_to_nat(0u);
v_bs_x27_2415_ = lean_array_uset(v_bs_2410_, v_i_2409_, v___x_2414_);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_add(v_i_2409_, v___x_2416_);
v___x_2418_ = lean_array_uset(v_bs_x27_2415_, v_i_2409_, v_v_2413_);
v_i_2409_ = v___x_2417_;
v_bs_2410_ = v___x_2418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2420_, lean_object* v_i_2421_, lean_object* v_bs_2422_){
_start:
{
size_t v_sz_boxed_2423_; size_t v_i_boxed_2424_; lean_object* v_res_2425_; 
v_sz_boxed_2423_ = lean_unbox_usize(v_sz_2420_);
lean_dec(v_sz_2420_);
v_i_boxed_2424_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_res_2425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2423_, v_i_boxed_2424_, v_bs_2422_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 4)
{
lean_object* v_elems_2427_; size_t v_sz_2428_; size_t v___x_2429_; lean_object* v___x_2430_; 
v_elems_2427_ = lean_ctor_get(v_x_2426_, 0);
lean_inc_ref(v_elems_2427_);
lean_dec_ref(v_x_2426_);
v_sz_2428_ = lean_array_size(v_elems_2427_);
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2428_, v___x_2429_, v_elems_2427_);
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2431_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2432_ = lean_unsigned_to_nat(80u);
v___x_2433_ = l_Lean_Json_pretty(v_x_2426_, v___x_2432_);
v___x_2434_ = lean_string_append(v___x_2431_, v___x_2433_);
lean_dec_ref(v___x_2433_);
v___x_2435_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2440_){
_start:
{
if (lean_obj_tag(v_x_2440_) == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2442_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2442_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2460_, lean_object* v_k_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_Lean_Json_getObjValD(v_j_2460_, v_k_2461_);
v___x_2463_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2464_, lean_object* v_k_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2464_, v_k_2465_);
lean_dec_ref(v_k_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2467_, lean_object* v_v_2468_, lean_object* v_t_2469_){
_start:
{
if (lean_obj_tag(v_t_2469_) == 0)
{
lean_object* v_size_2470_; lean_object* v_k_2471_; lean_object* v_v_2472_; lean_object* v_l_2473_; lean_object* v_r_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2754_; 
v_size_2470_ = lean_ctor_get(v_t_2469_, 0);
v_k_2471_ = lean_ctor_get(v_t_2469_, 1);
v_v_2472_ = lean_ctor_get(v_t_2469_, 2);
v_l_2473_ = lean_ctor_get(v_t_2469_, 3);
v_r_2474_ = lean_ctor_get(v_t_2469_, 4);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_t_2469_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2476_ = v_t_2469_;
v_isShared_2477_ = v_isSharedCheck_2754_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_r_2474_);
lean_inc(v_l_2473_);
lean_inc(v_v_2472_);
lean_inc(v_k_2471_);
lean_inc(v_size_2470_);
lean_dec(v_t_2469_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2754_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2467_, v_k_2471_);
switch(v___x_2478_)
{
case 0:
{
lean_object* v_impl_2479_; lean_object* v___x_2480_; 
lean_dec(v_size_2470_);
v_impl_2479_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2467_, v_v_2468_, v_l_2473_);
v___x_2480_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2474_) == 0)
{
lean_object* v_size_2481_; lean_object* v_size_2482_; lean_object* v_k_2483_; lean_object* v_v_2484_; lean_object* v_l_2485_; lean_object* v_r_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_size_2481_ = lean_ctor_get(v_r_2474_, 0);
v_size_2482_ = lean_ctor_get(v_impl_2479_, 0);
lean_inc(v_size_2482_);
v_k_2483_ = lean_ctor_get(v_impl_2479_, 1);
lean_inc(v_k_2483_);
v_v_2484_ = lean_ctor_get(v_impl_2479_, 2);
lean_inc(v_v_2484_);
v_l_2485_ = lean_ctor_get(v_impl_2479_, 3);
lean_inc(v_l_2485_);
v_r_2486_ = lean_ctor_get(v_impl_2479_, 4);
lean_inc(v_r_2486_);
v___x_2487_ = lean_unsigned_to_nat(3u);
v___x_2488_ = lean_nat_mul(v___x_2487_, v_size_2481_);
v___x_2489_ = lean_nat_dec_lt(v___x_2488_, v_size_2482_);
lean_dec(v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_r_2486_);
lean_dec(v_l_2485_);
lean_dec(v_v_2484_);
lean_dec(v_k_2483_);
v___x_2490_ = lean_nat_add(v___x_2480_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2491_ = lean_nat_add(v___x_2490_, v_size_2481_);
lean_dec(v___x_2490_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 3, v_impl_2479_);
lean_ctor_set(v___x_2476_, 0, v___x_2491_);
v___x_2493_ = v___x_2476_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_impl_2479_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_r_2474_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
else
{
lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2560_; 
v_isSharedCheck_2560_ = !lean_is_exclusive(v_impl_2479_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; lean_object* v_unused_2565_; 
v_unused_2561_ = lean_ctor_get(v_impl_2479_, 4);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_impl_2479_, 3);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_impl_2479_, 2);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_impl_2479_, 1);
lean_dec(v_unused_2564_);
v_unused_2565_ = lean_ctor_get(v_impl_2479_, 0);
lean_dec(v_unused_2565_);
v___x_2496_ = v_impl_2479_;
v_isShared_2497_ = v_isSharedCheck_2560_;
goto v_resetjp_2495_;
}
else
{
lean_dec(v_impl_2479_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2560_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_size_2498_; lean_object* v_size_2499_; lean_object* v_k_2500_; lean_object* v_v_2501_; lean_object* v_l_2502_; lean_object* v_r_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_size_2498_ = lean_ctor_get(v_l_2485_, 0);
v_size_2499_ = lean_ctor_get(v_r_2486_, 0);
v_k_2500_ = lean_ctor_get(v_r_2486_, 1);
v_v_2501_ = lean_ctor_get(v_r_2486_, 2);
v_l_2502_ = lean_ctor_get(v_r_2486_, 3);
v_r_2503_ = lean_ctor_get(v_r_2486_, 4);
v___x_2504_ = lean_unsigned_to_nat(2u);
v___x_2505_ = lean_nat_mul(v___x_2504_, v_size_2498_);
v___x_2506_ = lean_nat_dec_lt(v_size_2499_, v___x_2505_);
lean_dec(v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2535_; 
lean_inc(v_r_2503_);
lean_inc(v_l_2502_);
lean_inc(v_v_2501_);
lean_inc(v_k_2500_);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_r_2486_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2536_ = lean_ctor_get(v_r_2486_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_r_2486_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_r_2486_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_r_2486_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_r_2486_, 0);
lean_dec(v_unused_2540_);
v___x_2508_ = v_r_2486_;
v_isShared_2509_ = v_isSharedCheck_2535_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v_r_2486_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2535_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___x_2523_; lean_object* v___y_2525_; 
v___x_2510_ = lean_nat_add(v___x_2480_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2511_ = lean_nat_add(v___x_2510_, v_size_2481_);
lean_dec(v___x_2510_);
v___x_2523_ = lean_nat_add(v___x_2480_, v_size_2498_);
if (lean_obj_tag(v_l_2502_) == 0)
{
lean_object* v_size_2533_; 
v_size_2533_ = lean_ctor_get(v_l_2502_, 0);
lean_inc(v_size_2533_);
v___y_2525_ = v_size_2533_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v___y_2525_ = v___x_2534_;
goto v___jp_2524_;
}
v___jp_2512_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_nat_add(v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec(v___y_2514_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 4, v_r_2474_);
lean_ctor_set(v___x_2508_, 3, v_r_2503_);
lean_ctor_set(v___x_2508_, 2, v_v_2472_);
lean_ctor_set(v___x_2508_, 1, v_k_2471_);
lean_ctor_set(v___x_2508_, 0, v___x_2516_);
v___x_2518_ = v___x_2508_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_r_2503_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_r_2474_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 4, v___x_2518_);
lean_ctor_set(v___x_2496_, 3, v___y_2513_);
lean_ctor_set(v___x_2496_, 2, v_v_2501_);
lean_ctor_set(v___x_2496_, 1, v_k_2500_);
lean_ctor_set(v___x_2496_, 0, v___x_2511_);
v___x_2520_ = v___x_2496_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_k_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_v_2501_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v___y_2513_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_nat_add(v___x_2523_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec(v___x_2523_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_l_2502_);
lean_ctor_set(v___x_2476_, 3, v_l_2485_);
lean_ctor_set(v___x_2476_, 2, v_v_2484_);
lean_ctor_set(v___x_2476_, 1, v_k_2483_);
lean_ctor_set(v___x_2476_, 0, v___x_2526_);
v___x_2528_ = v___x_2476_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_k_2483_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_v_2484_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_l_2485_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_l_2502_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_nat_add(v___x_2480_, v_size_2481_);
if (lean_obj_tag(v_r_2503_) == 0)
{
lean_object* v_size_2530_; 
v_size_2530_ = lean_ctor_get(v_r_2503_, 0);
lean_inc(v_size_2530_);
v___y_2513_ = v___x_2528_;
v___y_2514_ = v___x_2529_;
v___y_2515_ = v_size_2530_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___y_2513_ = v___x_2528_;
v___y_2514_ = v___x_2529_;
v___y_2515_ = v___x_2531_;
goto v___jp_2512_;
}
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
lean_del_object(v___x_2476_);
v___x_2541_ = lean_nat_add(v___x_2480_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2542_ = lean_nat_add(v___x_2541_, v_size_2481_);
lean_dec(v___x_2541_);
v___x_2543_ = lean_nat_add(v___x_2480_, v_size_2481_);
v___x_2544_ = lean_nat_add(v___x_2543_, v_size_2499_);
lean_dec(v___x_2543_);
lean_inc_ref(v_r_2474_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 4, v_r_2474_);
lean_ctor_set(v___x_2496_, 3, v_r_2486_);
lean_ctor_set(v___x_2496_, 2, v_v_2472_);
lean_ctor_set(v___x_2496_, 1, v_k_2471_);
lean_ctor_set(v___x_2496_, 0, v___x_2544_);
v___x_2546_ = v___x_2496_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_r_2486_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_r_2474_);
v___x_2546_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v_r_2474_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; lean_object* v_unused_2555_; lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; 
v_unused_2554_ = lean_ctor_get(v_r_2474_, 4);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_r_2474_, 3);
lean_dec(v_unused_2555_);
v_unused_2556_ = lean_ctor_get(v_r_2474_, 2);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_r_2474_, 1);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_r_2474_, 0);
lean_dec(v_unused_2558_);
v___x_2548_ = v_r_2474_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_dec(v_r_2474_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 4, v___x_2546_);
lean_ctor_set(v___x_2548_, 3, v_l_2485_);
lean_ctor_set(v___x_2548_, 2, v_v_2484_);
lean_ctor_set(v___x_2548_, 1, v_k_2483_);
lean_ctor_set(v___x_2548_, 0, v___x_2542_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2483_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2484_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_l_2485_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v___x_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2566_; 
v_l_2566_ = lean_ctor_get(v_impl_2479_, 3);
lean_inc(v_l_2566_);
if (lean_obj_tag(v_l_2566_) == 0)
{
lean_object* v_r_2567_; lean_object* v_k_2568_; lean_object* v_v_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2580_; 
v_r_2567_ = lean_ctor_get(v_impl_2479_, 4);
v_k_2568_ = lean_ctor_get(v_impl_2479_, 1);
v_v_2569_ = lean_ctor_get(v_impl_2479_, 2);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_impl_2479_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; 
v_unused_2581_ = lean_ctor_get(v_impl_2479_, 3);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_impl_2479_, 0);
lean_dec(v_unused_2582_);
v___x_2571_ = v_impl_2479_;
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_r_2567_);
lean_inc(v_v_2569_);
lean_inc(v_k_2568_);
lean_dec(v_impl_2479_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2580_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2567_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 3, v_r_2567_);
lean_ctor_set(v___x_2571_, 2, v_v_2472_);
lean_ctor_set(v___x_2571_, 1, v_k_2471_);
lean_ctor_set(v___x_2571_, 0, v___x_2480_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_r_2567_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v___x_2575_);
lean_ctor_set(v___x_2476_, 3, v_l_2566_);
lean_ctor_set(v___x_2476_, 2, v_v_2569_);
lean_ctor_set(v___x_2476_, 1, v_k_2568_);
lean_ctor_set(v___x_2476_, 0, v___x_2573_);
v___x_2577_ = v___x_2476_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2568_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2569_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_l_2566_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v_r_2583_; 
v_r_2583_ = lean_ctor_get(v_impl_2479_, 4);
lean_inc(v_r_2583_);
if (lean_obj_tag(v_r_2583_) == 0)
{
lean_object* v_k_2584_; lean_object* v_v_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2608_; 
v_k_2584_ = lean_ctor_get(v_impl_2479_, 1);
v_v_2585_ = lean_ctor_get(v_impl_2479_, 2);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_impl_2479_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; 
v_unused_2609_ = lean_ctor_get(v_impl_2479_, 4);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_impl_2479_, 3);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_impl_2479_, 0);
lean_dec(v_unused_2611_);
v___x_2587_ = v_impl_2479_;
v_isShared_2588_ = v_isSharedCheck_2608_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_v_2585_);
lean_inc(v_k_2584_);
lean_dec(v_impl_2479_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2608_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_k_2589_; lean_object* v_v_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2604_; 
v_k_2589_ = lean_ctor_get(v_r_2583_, 1);
v_v_2590_ = lean_ctor_get(v_r_2583_, 2);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_r_2583_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; lean_object* v_unused_2606_; lean_object* v_unused_2607_; 
v_unused_2605_ = lean_ctor_get(v_r_2583_, 4);
lean_dec(v_unused_2605_);
v_unused_2606_ = lean_ctor_get(v_r_2583_, 3);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v_r_2583_, 0);
lean_dec(v_unused_2607_);
v___x_2592_ = v_r_2583_;
v_isShared_2593_ = v_isSharedCheck_2604_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_v_2590_);
lean_inc(v_k_2589_);
lean_dec(v_r_2583_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2604_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_unsigned_to_nat(3u);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v_l_2566_);
lean_ctor_set(v___x_2592_, 3, v_l_2566_);
lean_ctor_set(v___x_2592_, 2, v_v_2585_);
lean_ctor_set(v___x_2592_, 1, v_k_2584_);
lean_ctor_set(v___x_2592_, 0, v___x_2480_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2584_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2585_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_l_2566_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_l_2566_);
v___x_2596_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 4, v_l_2566_);
lean_ctor_set(v___x_2587_, 2, v_v_2472_);
lean_ctor_set(v___x_2587_, 1, v_k_2471_);
lean_ctor_set(v___x_2587_, 0, v___x_2480_);
v___x_2598_ = v___x_2587_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_l_2566_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_l_2566_);
v___x_2598_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v___x_2598_);
lean_ctor_set(v___x_2476_, 3, v___x_2596_);
lean_ctor_set(v___x_2476_, 2, v_v_2590_);
lean_ctor_set(v___x_2476_, 1, v_k_2589_);
lean_ctor_set(v___x_2476_, 0, v___x_2594_);
v___x_2600_ = v___x_2476_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2589_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2590_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v___x_2598_);
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
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_unsigned_to_nat(2u);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_r_2583_);
lean_ctor_set(v___x_2476_, 3, v_impl_2479_);
lean_ctor_set(v___x_2476_, 0, v___x_2612_);
v___x_2614_ = v___x_2476_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_impl_2479_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_r_2583_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2617_; 
lean_dec(v_v_2472_);
lean_dec(v_k_2471_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 2, v_v_2468_);
lean_ctor_set(v___x_2476_, 1, v_k_2467_);
v___x_2617_ = v___x_2476_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_size_2470_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_k_2467_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_v_2468_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_l_2473_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_r_2474_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
default: 
{
lean_object* v_impl_2619_; lean_object* v___x_2620_; 
lean_dec(v_size_2470_);
v_impl_2619_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2467_, v_v_2468_, v_r_2474_);
v___x_2620_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2473_) == 0)
{
lean_object* v_size_2621_; lean_object* v_size_2622_; lean_object* v_k_2623_; lean_object* v_v_2624_; lean_object* v_l_2625_; lean_object* v_r_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_size_2621_ = lean_ctor_get(v_l_2473_, 0);
v_size_2622_ = lean_ctor_get(v_impl_2619_, 0);
lean_inc(v_size_2622_);
v_k_2623_ = lean_ctor_get(v_impl_2619_, 1);
lean_inc(v_k_2623_);
v_v_2624_ = lean_ctor_get(v_impl_2619_, 2);
lean_inc(v_v_2624_);
v_l_2625_ = lean_ctor_get(v_impl_2619_, 3);
lean_inc(v_l_2625_);
v_r_2626_ = lean_ctor_get(v_impl_2619_, 4);
lean_inc(v_r_2626_);
v___x_2627_ = lean_unsigned_to_nat(3u);
v___x_2628_ = lean_nat_mul(v___x_2627_, v_size_2621_);
v___x_2629_ = lean_nat_dec_lt(v___x_2628_, v_size_2622_);
lean_dec(v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
lean_dec(v_r_2626_);
lean_dec(v_l_2625_);
lean_dec(v_v_2624_);
lean_dec(v_k_2623_);
v___x_2630_ = lean_nat_add(v___x_2620_, v_size_2621_);
v___x_2631_ = lean_nat_add(v___x_2630_, v_size_2622_);
lean_dec(v_size_2622_);
lean_dec(v___x_2630_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_impl_2619_);
lean_ctor_set(v___x_2476_, 0, v___x_2631_);
v___x_2633_ = v___x_2476_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_l_2473_);
lean_ctor_set(v_reuseFailAlloc_2634_, 4, v_impl_2619_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
else
{
lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2698_; 
v_isSharedCheck_2698_ = !lean_is_exclusive(v_impl_2619_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; lean_object* v_unused_2700_; lean_object* v_unused_2701_; lean_object* v_unused_2702_; lean_object* v_unused_2703_; 
v_unused_2699_ = lean_ctor_get(v_impl_2619_, 4);
lean_dec(v_unused_2699_);
v_unused_2700_ = lean_ctor_get(v_impl_2619_, 3);
lean_dec(v_unused_2700_);
v_unused_2701_ = lean_ctor_get(v_impl_2619_, 2);
lean_dec(v_unused_2701_);
v_unused_2702_ = lean_ctor_get(v_impl_2619_, 1);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_impl_2619_, 0);
lean_dec(v_unused_2703_);
v___x_2636_ = v_impl_2619_;
v_isShared_2637_ = v_isSharedCheck_2698_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v_impl_2619_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2698_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_size_2638_; lean_object* v_k_2639_; lean_object* v_v_2640_; lean_object* v_l_2641_; lean_object* v_r_2642_; lean_object* v_size_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v_size_2638_ = lean_ctor_get(v_l_2625_, 0);
v_k_2639_ = lean_ctor_get(v_l_2625_, 1);
v_v_2640_ = lean_ctor_get(v_l_2625_, 2);
v_l_2641_ = lean_ctor_get(v_l_2625_, 3);
v_r_2642_ = lean_ctor_get(v_l_2625_, 4);
v_size_2643_ = lean_ctor_get(v_r_2626_, 0);
v___x_2644_ = lean_unsigned_to_nat(2u);
v___x_2645_ = lean_nat_mul(v___x_2644_, v_size_2643_);
v___x_2646_ = lean_nat_dec_lt(v_size_2638_, v___x_2645_);
lean_dec(v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2674_; 
lean_inc(v_r_2642_);
lean_inc(v_l_2641_);
lean_inc(v_v_2640_);
lean_inc(v_k_2639_);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_l_2625_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; lean_object* v_unused_2678_; lean_object* v_unused_2679_; 
v_unused_2675_ = lean_ctor_get(v_l_2625_, 4);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2625_, 3);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_l_2625_, 2);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_l_2625_, 1);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2625_, 0);
lean_dec(v_unused_2679_);
v___x_2648_ = v_l_2625_;
v_isShared_2649_ = v_isSharedCheck_2674_;
goto v_resetjp_2647_;
}
else
{
lean_dec(v_l_2625_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2674_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2664_; 
v___x_2650_ = lean_nat_add(v___x_2620_, v_size_2621_);
v___x_2651_ = lean_nat_add(v___x_2650_, v_size_2622_);
lean_dec(v_size_2622_);
if (lean_obj_tag(v_l_2641_) == 0)
{
lean_object* v_size_2672_; 
v_size_2672_ = lean_ctor_get(v_l_2641_, 0);
lean_inc(v_size_2672_);
v___y_2664_ = v_size_2672_;
goto v___jp_2663_;
}
else
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___y_2664_ = v___x_2673_;
goto v___jp_2663_;
}
v___jp_2652_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = lean_nat_add(v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec(v___y_2654_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 4, v_r_2626_);
lean_ctor_set(v___x_2648_, 3, v_r_2642_);
lean_ctor_set(v___x_2648_, 2, v_v_2624_);
lean_ctor_set(v___x_2648_, 1, v_k_2623_);
lean_ctor_set(v___x_2648_, 0, v___x_2656_);
v___x_2658_ = v___x_2648_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_k_2623_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_v_2624_);
lean_ctor_set(v_reuseFailAlloc_2662_, 3, v_r_2642_);
lean_ctor_set(v_reuseFailAlloc_2662_, 4, v_r_2626_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 4, v___x_2658_);
lean_ctor_set(v___x_2636_, 3, v___y_2653_);
lean_ctor_set(v___x_2636_, 2, v_v_2640_);
lean_ctor_set(v___x_2636_, 1, v_k_2639_);
lean_ctor_set(v___x_2636_, 0, v___x_2651_);
v___x_2660_ = v___x_2636_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_k_2639_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_v_2640_);
lean_ctor_set(v_reuseFailAlloc_2661_, 3, v___y_2653_);
lean_ctor_set(v_reuseFailAlloc_2661_, 4, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = lean_nat_add(v___x_2650_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec(v___x_2650_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_l_2641_);
lean_ctor_set(v___x_2476_, 0, v___x_2665_);
v___x_2667_ = v___x_2476_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_l_2473_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_l_2641_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_nat_add(v___x_2620_, v_size_2643_);
if (lean_obj_tag(v_r_2642_) == 0)
{
lean_object* v_size_2669_; 
v_size_2669_ = lean_ctor_get(v_r_2642_, 0);
lean_inc(v_size_2669_);
v___y_2653_ = v___x_2667_;
v___y_2654_ = v___x_2668_;
v___y_2655_ = v_size_2669_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_unsigned_to_nat(0u);
v___y_2653_ = v___x_2667_;
v___y_2654_ = v___x_2668_;
v___y_2655_ = v___x_2670_;
goto v___jp_2652_;
}
}
}
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_del_object(v___x_2476_);
v___x_2680_ = lean_nat_add(v___x_2620_, v_size_2621_);
v___x_2681_ = lean_nat_add(v___x_2680_, v_size_2622_);
lean_dec(v_size_2622_);
v___x_2682_ = lean_nat_add(v___x_2680_, v_size_2638_);
lean_dec(v___x_2680_);
lean_inc_ref(v_l_2473_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 4, v_l_2625_);
lean_ctor_set(v___x_2636_, 3, v_l_2473_);
lean_ctor_set(v___x_2636_, 2, v_v_2472_);
lean_ctor_set(v___x_2636_, 1, v_k_2471_);
lean_ctor_set(v___x_2636_, 0, v___x_2682_);
v___x_2684_ = v___x_2636_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_l_2473_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_l_2625_);
v___x_2684_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_isSharedCheck_2691_ = !lean_is_exclusive(v_l_2473_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; lean_object* v_unused_2693_; lean_object* v_unused_2694_; lean_object* v_unused_2695_; lean_object* v_unused_2696_; 
v_unused_2692_ = lean_ctor_get(v_l_2473_, 4);
lean_dec(v_unused_2692_);
v_unused_2693_ = lean_ctor_get(v_l_2473_, 3);
lean_dec(v_unused_2693_);
v_unused_2694_ = lean_ctor_get(v_l_2473_, 2);
lean_dec(v_unused_2694_);
v_unused_2695_ = lean_ctor_get(v_l_2473_, 1);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_l_2473_, 0);
lean_dec(v_unused_2696_);
v___x_2686_ = v_l_2473_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_l_2473_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 4, v_r_2626_);
lean_ctor_set(v___x_2686_, 3, v___x_2684_);
lean_ctor_set(v___x_2686_, 2, v_v_2624_);
lean_ctor_set(v___x_2686_, 1, v_k_2623_);
lean_ctor_set(v___x_2686_, 0, v___x_2681_);
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_k_2623_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_v_2624_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v_r_2626_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2704_; 
v_l_2704_ = lean_ctor_get(v_impl_2619_, 3);
lean_inc(v_l_2704_);
if (lean_obj_tag(v_l_2704_) == 0)
{
lean_object* v_r_2705_; lean_object* v_k_2706_; lean_object* v_v_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2730_; 
v_r_2705_ = lean_ctor_get(v_impl_2619_, 4);
v_k_2706_ = lean_ctor_get(v_impl_2619_, 1);
v_v_2707_ = lean_ctor_get(v_impl_2619_, 2);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_impl_2619_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2731_ = lean_ctor_get(v_impl_2619_, 3);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_impl_2619_, 0);
lean_dec(v_unused_2732_);
v___x_2709_ = v_impl_2619_;
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_r_2705_);
lean_inc(v_v_2707_);
lean_inc(v_k_2706_);
lean_dec(v_impl_2619_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_k_2711_; lean_object* v_v_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2726_; 
v_k_2711_ = lean_ctor_get(v_l_2704_, 1);
v_v_2712_ = lean_ctor_get(v_l_2704_, 2);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_l_2704_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; lean_object* v_unused_2728_; lean_object* v_unused_2729_; 
v_unused_2727_ = lean_ctor_get(v_l_2704_, 4);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_l_2704_, 3);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_l_2704_, 0);
lean_dec(v_unused_2729_);
v___x_2714_ = v_l_2704_;
v_isShared_2715_ = v_isSharedCheck_2726_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_v_2712_);
lean_inc(v_k_2711_);
lean_dec(v_l_2704_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2726_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2705_, 2);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 4, v_r_2705_);
lean_ctor_set(v___x_2714_, 3, v_r_2705_);
lean_ctor_set(v___x_2714_, 2, v_v_2472_);
lean_ctor_set(v___x_2714_, 1, v_k_2471_);
lean_ctor_set(v___x_2714_, 0, v___x_2620_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_r_2705_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_r_2705_);
v___x_2718_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
lean_inc(v_r_2705_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 3, v_r_2705_);
lean_ctor_set(v___x_2709_, 0, v___x_2620_);
v___x_2720_ = v___x_2709_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_k_2706_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_v_2707_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_r_2705_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_r_2705_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v___x_2720_);
lean_ctor_set(v___x_2476_, 3, v___x_2718_);
lean_ctor_set(v___x_2476_, 2, v_v_2712_);
lean_ctor_set(v___x_2476_, 1, v_k_2711_);
lean_ctor_set(v___x_2476_, 0, v___x_2716_);
v___x_2722_ = v___x_2476_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_k_2711_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_v_2712_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2723_, 4, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
else
{
lean_object* v_r_2733_; 
v_r_2733_ = lean_ctor_get(v_impl_2619_, 4);
lean_inc(v_r_2733_);
if (lean_obj_tag(v_r_2733_) == 0)
{
lean_object* v_k_2734_; lean_object* v_v_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
v_k_2734_ = lean_ctor_get(v_impl_2619_, 1);
v_v_2735_ = lean_ctor_get(v_impl_2619_, 2);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_impl_2619_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; 
v_unused_2747_ = lean_ctor_get(v_impl_2619_, 4);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_impl_2619_, 3);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_impl_2619_, 0);
lean_dec(v_unused_2749_);
v___x_2737_ = v_impl_2619_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_v_2735_);
lean_inc(v_k_2734_);
lean_dec(v_impl_2619_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_unsigned_to_nat(3u);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 4, v_l_2704_);
lean_ctor_set(v___x_2737_, 2, v_v_2472_);
lean_ctor_set(v___x_2737_, 1, v_k_2471_);
lean_ctor_set(v___x_2737_, 0, v___x_2620_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_l_2704_);
lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_l_2704_);
v___x_2741_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2743_; 
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_r_2733_);
lean_ctor_set(v___x_2476_, 3, v___x_2741_);
lean_ctor_set(v___x_2476_, 2, v_v_2735_);
lean_ctor_set(v___x_2476_, 1, v_k_2734_);
lean_ctor_set(v___x_2476_, 0, v___x_2739_);
v___x_2743_ = v___x_2476_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_k_2734_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_v_2735_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_r_2733_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_unsigned_to_nat(2u);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_impl_2619_);
lean_ctor_set(v___x_2476_, 3, v_r_2733_);
lean_ctor_set(v___x_2476_, 0, v___x_2750_);
v___x_2752_ = v___x_2476_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_k_2471_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_v_2472_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_r_2733_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_impl_2619_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
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
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v_k_2467_);
lean_ctor_set(v___x_2756_, 2, v_v_2468_);
lean_ctor_set(v___x_2756_, 3, v_t_2469_);
lean_ctor_set(v___x_2756_, 4, v_t_2469_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2757_, size_t v_i_2758_, lean_object* v_bs_2759_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_lt(v_i_2758_, v_sz_2757_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_bs_2759_);
return v___x_2761_;
}
else
{
lean_object* v_v_2762_; lean_object* v___x_2763_; lean_object* v_bs_x27_2764_; lean_object* v_a_2766_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2837_; 
v_v_2762_ = lean_array_uget(v_bs_2759_, v_i_2758_);
v___x_2763_ = lean_unsigned_to_nat(0u);
v_bs_x27_2764_ = lean_array_uset(v_bs_2759_, v_i_2758_, v___x_2763_);
v___x_2771_ = lean_array_get_size(v_v_2762_);
v___x_2772_ = lean_unsigned_to_nat(4u);
v___x_2837_ = lean_nat_dec_eq(v___x_2771_, v___x_2772_);
if (v___x_2837_ == 0)
{
if (v___x_2760_ == 0)
{
goto v___jp_2773_;
}
else
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_unsigned_to_nat(5u);
v___x_2839_ = lean_nat_dec_eq(v___x_2771_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec_ref(v_bs_x27_2764_);
lean_dec(v_v_2762_);
v___x_2840_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2841_ = l_Nat_reprFast(v___x_2771_);
v___x_2842_ = lean_string_append(v___x_2840_, v___x_2841_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
else
{
goto v___jp_2773_;
}
}
}
else
{
goto v___jp_2773_;
}
v___jp_2765_:
{
size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((size_t)1ULL);
v___x_2768_ = lean_usize_add(v_i_2758_, v___x_2767_);
v___x_2769_ = lean_array_uset(v_bs_x27_2764_, v_i_2758_, v_a_2766_);
v_i_2758_ = v___x_2768_;
v_bs_2759_ = v___x_2769_;
goto _start;
}
v___jp_2773_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_array_fget_borrowed(v_v_2762_, v___x_2763_);
lean_inc(v___x_2774_);
v___x_2775_ = l_Lean_Json_getNat_x3f(v___x_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_bs_x27_2764_);
lean_dec(v_v_2762_);
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_a_2784_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2775_);
v___x_2785_ = lean_unsigned_to_nat(1u);
v___x_2786_ = lean_array_fget_borrowed(v_v_2762_, v___x_2785_);
lean_inc(v___x_2786_);
v___x_2787_ = l_Lean_Json_getNat_x3f(v___x_2786_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2784_);
lean_dec_ref(v_bs_x27_2764_);
lean_dec(v_v_2762_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2796_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2787_);
v___x_2797_ = lean_unsigned_to_nat(2u);
v___x_2798_ = lean_array_fget_borrowed(v_v_2762_, v___x_2797_);
lean_inc(v___x_2798_);
v___x_2799_ = l_Lean_Json_getNat_x3f(v___x_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2784_);
lean_dec_ref(v_bs_x27_2764_);
lean_dec(v_v_2762_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2808_);
lean_dec_ref(v___x_2799_);
v___x_2809_ = lean_unsigned_to_nat(3u);
v___x_2810_ = lean_array_fget_borrowed(v_v_2762_, v___x_2809_);
lean_inc(v___x_2810_);
v___x_2811_ = l_Lean_Json_getNat_x3f(v___x_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2808_);
lean_dec(v_a_2796_);
lean_dec(v_a_2784_);
lean_dec_ref(v_bs_x27_2764_);
lean_dec(v_v_2762_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_a_2820_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2811_);
v___x_2821_ = lean_unsigned_to_nat(5u);
v___x_2822_ = lean_nat_dec_eq(v___x_2771_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v_v_2762_);
v___x_2823_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2784_);
lean_ctor_set(v___x_2824_, 1, v_a_2796_);
lean_ctor_set(v___x_2824_, 2, v_a_2808_);
lean_ctor_set(v___x_2824_, 3, v_a_2820_);
lean_ctor_set(v___x_2824_, 4, v___x_2823_);
v_a_2766_ = v___x_2824_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_array_fget(v_v_2762_, v___x_2772_);
lean_dec(v_v_2762_);
v___x_2826_ = l_Lean_Json_getStr_x3f(v___x_2825_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2820_);
lean_dec(v_a_2808_);
lean_dec(v_a_2796_);
lean_dec(v_a_2784_);
lean_dec_ref(v_bs_x27_2764_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2826_);
v___x_2836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2784_);
lean_ctor_set(v___x_2836_, 1, v_a_2796_);
lean_ctor_set(v___x_2836_, 2, v_a_2808_);
lean_ctor_set(v___x_2836_, 3, v_a_2820_);
lean_ctor_set(v___x_2836_, 4, v_a_2835_);
v_a_2766_ = v___x_2836_;
goto v___jp_2765_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2844_, lean_object* v_i_2845_, lean_object* v_bs_2846_){
_start:
{
size_t v_sz_boxed_2847_; size_t v_i_boxed_2848_; lean_object* v_res_2849_; 
v_sz_boxed_2847_ = lean_unbox_usize(v_sz_2844_);
lean_dec(v_sz_2844_);
v_i_boxed_2848_ = lean_unbox_usize(v_i_2845_);
lean_dec(v_i_2845_);
v_res_2849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2847_, v_i_boxed_2848_, v_bs_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2850_, size_t v_i_2851_, lean_object* v_bs_2852_){
_start:
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_usize_dec_lt(v_i_2851_, v_sz_2850_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_bs_2852_);
return v___x_2854_;
}
else
{
lean_object* v_v_2855_; lean_object* v___x_2856_; 
v_v_2855_ = lean_array_uget_borrowed(v_bs_2852_, v_i_2851_);
lean_inc(v_v_2855_);
v___x_2856_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_bs_2852_);
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v_bs_x27_2867_; size_t v___x_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v_a_2865_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2856_);
v___x_2866_ = lean_unsigned_to_nat(0u);
v_bs_x27_2867_ = lean_array_uset(v_bs_2852_, v_i_2851_, v___x_2866_);
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2851_, v___x_2868_);
v___x_2870_ = lean_array_uset(v_bs_x27_2867_, v_i_2851_, v_a_2865_);
v_i_2851_ = v___x_2869_;
v_bs_2852_ = v___x_2870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_bs_2874_){
_start:
{
size_t v_sz_boxed_2875_; size_t v_i_boxed_2876_; lean_object* v_res_2877_; 
v_sz_boxed_2875_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2876_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2875_, v_i_boxed_2876_, v_bs_2874_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2878_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 4)
{
lean_object* v_elems_2879_; size_t v_sz_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v_elems_2879_ = lean_ctor_get(v_x_2878_, 0);
lean_inc_ref(v_elems_2879_);
lean_dec_ref(v_x_2878_);
v_sz_2880_ = lean_array_size(v_elems_2879_);
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2880_, v___x_2881_, v_elems_2879_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2883_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2884_ = lean_unsigned_to_nat(80u);
v___x_2885_ = l_Lean_Json_pretty(v_x_2878_, v___x_2884_);
v___x_2886_ = lean_string_append(v___x_2883_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
return v___x_2889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2890_, lean_object* v_k_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = l_Lean_Json_getObjValD(v_j_2890_, v_k_2891_);
v___x_2893_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2894_, lean_object* v_k_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2894_, v_k_2895_);
lean_dec_ref(v_k_2895_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2897_, lean_object* v_x_2898_){
_start:
{
if (lean_obj_tag(v_x_2898_) == 0)
{
lean_object* v_k_2899_; lean_object* v_v_2900_; lean_object* v_l_2901_; lean_object* v_r_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_3062_; 
v_k_2899_ = lean_ctor_get(v_x_2898_, 1);
v_v_2900_ = lean_ctor_get(v_x_2898_, 2);
v_l_2901_ = lean_ctor_get(v_x_2898_, 3);
v_r_2902_ = lean_ctor_get(v_x_2898_, 4);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_x_2898_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_x_2898_, 0);
lean_dec(v_unused_3063_);
v___x_2904_ = v_x_2898_;
v_isShared_2905_ = v_isSharedCheck_3062_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_r_2902_);
lean_inc(v_l_2901_);
lean_inc(v_v_2900_);
lean_inc(v_k_2899_);
lean_dec(v_x_2898_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_3062_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2897_, v_l_2901_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
lean_dec(v_k_2899_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3061_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_3061_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3061_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Json_parse(v_k_2899_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2921_; 
v_a_2920_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2920_);
lean_dec_ref(v___x_2911_);
v___x_2921_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2920_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v_definition_x3f_2932_; lean_object* v_a_2960_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_a_2930_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2921_);
v___x_2964_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2900_);
v___x_2965_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2900_, v___x_2964_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3060_; 
v_a_2974_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_2976_ = v___x_2965_;
v_isShared_2977_ = v_isSharedCheck_3060_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2965_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3060_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
if (lean_obj_tag(v_a_2974_) == 0)
{
lean_object* v___x_2978_; 
lean_del_object(v___x_2976_);
lean_del_object(v___x_2909_);
lean_del_object(v___x_2904_);
v___x_2978_ = lean_box(0);
v_definition_x3f_2932_ = v___x_2978_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_3051_; 
v_val_2979_ = lean_ctor_get(v_a_2974_, 0);
lean_inc(v_val_2979_);
lean_dec_ref(v_a_2974_);
v___x_2980_ = lean_array_get_size(v_val_2979_);
v___x_2981_ = lean_unsigned_to_nat(4u);
v___x_3051_ = lean_nat_dec_eq(v___x_2980_, v___x_2981_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(5u);
v___x_3053_ = lean_nat_dec_eq(v___x_2980_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
lean_dec(v_val_2979_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v___x_3054_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_3055_ = l_Nat_reprFast(v___x_2980_);
v___x_3056_ = lean_string_append(v___x_3054_, v___x_3055_);
lean_dec_ref(v___x_3055_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set_tag(v___x_2976_, 0);
lean_ctor_set(v___x_2976_, 0, v___x_3056_);
v___x_3058_ = v___x_2976_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_del_object(v___x_2976_);
goto v___jp_2982_;
}
}
else
{
lean_del_object(v___x_2976_);
goto v___jp_2982_;
}
v___jp_2982_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_array_fget_borrowed(v_val_2979_, v___x_2983_);
lean_inc(v___x_2984_);
v___x_2985_ = l_Lean_Json_getNat_x3f(v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_val_2979_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2994_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2985_);
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_array_fget_borrowed(v_val_2979_, v___x_2995_);
lean_inc(v___x_2996_);
v___x_2997_ = l_Lean_Json_getNat_x3f(v___x_2996_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_a_2994_);
lean_dec(v_val_2979_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
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
lean_dec_ref(v___x_2997_);
v___x_3007_ = lean_unsigned_to_nat(2u);
v___x_3008_ = lean_array_fget_borrowed(v_val_2979_, v___x_3007_);
lean_inc(v___x_3008_);
v___x_3009_ = l_Lean_Json_getNat_x3f(v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v_a_3006_);
lean_dec(v_a_2994_);
lean_dec(v_val_2979_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
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
lean_dec_ref(v___x_3009_);
v___x_3019_ = lean_unsigned_to_nat(3u);
v___x_3020_ = lean_array_fget_borrowed(v_val_2979_, v___x_3019_);
lean_inc(v___x_3020_);
v___x_3021_ = l_Lean_Json_getNat_x3f(v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_3018_);
lean_dec(v_a_3006_);
lean_dec(v_a_2994_);
lean_dec(v_val_2979_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
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
lean_object* v_a_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v_a_3030_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3021_);
v___x_3031_ = lean_unsigned_to_nat(5u);
v___x_3032_ = lean_nat_dec_eq(v___x_2980_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_val_2979_);
v___x_3033_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 4, v___x_3033_);
lean_ctor_set(v___x_2904_, 3, v_a_3030_);
lean_ctor_set(v___x_2904_, 2, v_a_3018_);
lean_ctor_set(v___x_2904_, 1, v_a_3006_);
lean_ctor_set(v___x_2904_, 0, v_a_2994_);
v___x_3035_ = v___x_2904_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_2994_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3006_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v_a_2960_ = v___x_3035_;
goto v___jp_2959_;
}
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_array_fget(v_val_2979_, v___x_2981_);
lean_dec(v_val_2979_);
v___x_3038_ = l_Lean_Json_getStr_x3f(v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_a_3030_);
lean_dec(v_a_3018_);
lean_dec(v_a_3006_);
lean_dec(v_a_2994_);
lean_dec(v_a_2930_);
lean_del_object(v___x_2909_);
lean_dec(v_a_2907_);
lean_del_object(v___x_2904_);
lean_dec(v_r_2902_);
lean_dec(v_v_2900_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; 
v_a_3047_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3038_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 4, v_a_3047_);
lean_ctor_set(v___x_2904_, 3, v_a_3030_);
lean_ctor_set(v___x_2904_, 2, v_a_3018_);
lean_ctor_set(v___x_2904_, 1, v_a_3006_);
lean_ctor_set(v___x_2904_, 0, v_a_2994_);
v___x_3049_ = v___x_2904_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_2994_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_a_3006_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v_a_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v_a_2960_ = v___x_3049_;
goto v___jp_2959_;
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
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2934_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2900_, v___x_2933_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v_definition_x3f_2932_);
lean_dec(v_a_2930_);
lean_dec(v_a_2907_);
lean_dec(v_r_2902_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
else
{
lean_object* v_a_2943_; size_t v_sz_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v_a_2943_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2934_);
v_sz_2944_ = lean_array_size(v_a_2943_);
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2944_, v___x_2945_, v_a_2943_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_definition_x3f_2932_);
lean_dec(v_a_2930_);
lean_dec(v_a_2907_);
lean_dec(v_r_2902_);
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
lean_object* v_a_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_a_2955_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2946_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v_definition_x3f_2932_);
lean_ctor_set(v___x_2956_, 1, v_a_2955_);
v___x_2957_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2930_, v___x_2956_, v_a_2907_);
v_init_2897_ = v___x_2957_;
v_x_2898_ = v_r_2902_;
goto _start;
}
}
}
v___jp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v_a_2960_);
v___x_2962_ = v___x_2909_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v_definition_x3f_2932_ = v___x_2962_;
goto v___jp_2931_;
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
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v_init_2897_);
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3065_, lean_object* v_k_3066_){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = l_Lean_Json_getObjValD(v_j_3065_, v_k_3066_);
v___x_3068_ = l_Lean_Json_getObj_x3f(v___x_3067_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3077_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v___x_3068_);
v___x_3078_ = lean_box(1);
v___x_3079_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3078_, v_a_3077_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3080_, lean_object* v_k_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3080_, v_k_3081_);
lean_dec_ref(v_k_3081_);
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = 1;
v___x_3089_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3090_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3089_, v___x_3088_);
return v___x_3090_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3092_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3093_ = lean_string_append(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3095_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3096_ = lean_string_append(v___x_3095_, v___x_3094_);
return v___x_3096_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3099_ = lean_string_append(v___x_3098_, v___x_3097_);
return v___x_3099_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = 1;
v___x_3104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3108_ = lean_string_append(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3111_ = lean_string_append(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = 1;
v___x_3116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3116_, v___x_3115_);
return v___x_3117_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3120_ = lean_string_append(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3123_ = lean_string_append(v___x_3122_, v___x_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3124_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3124_);
v___x_3126_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3124_, v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_json_3124_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3136_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3132_ = lean_string_append(v___x_3131_, v_a_3127_);
lean_dec(v_a_3127_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3132_);
v___x_3134_ = v___x_3129_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_json_3124_);
v_a_3137_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3126_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3126_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 0);
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3126_);
v___x_3146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3124_);
v___x_3147_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3124_, v___x_3146_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_a_3145_);
lean_dec(v_json_3124_);
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
v___x_3152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
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
lean_dec(v_a_3145_);
lean_dec(v_json_3124_);
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
lean_dec_ref(v___x_3147_);
v___x_3167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3168_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3124_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3166_);
lean_dec(v_a_3145_);
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
v___x_3173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
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
lean_dec(v_a_3145_);
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
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3195_; 
v_a_3187_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3189_ = v___x_3168_;
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3168_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3195_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3145_);
lean_ctor_set(v___x_3191_, 1, v_a_3166_);
lean_ctor_set(v___x_3191_, 2, v_a_3187_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3191_);
v___x_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3196_, lean_object* v_k_3197_, lean_object* v_v_3198_, lean_object* v_t_3199_, lean_object* v_hl_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3197_, v_v_3198_, v_t_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3202_, lean_object* v_k_3203_, lean_object* v_v_3204_, lean_object* v_t_3205_, lean_object* v_hl_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3203_, v_v_3204_, v_t_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3210_, lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 0)
{
lean_object* v_k_3212_; lean_object* v_v_3213_; lean_object* v_l_3214_; lean_object* v_r_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_k_3212_ = lean_ctor_get(v_x_3211_, 1);
v_v_3213_ = lean_ctor_get(v_x_3211_, 2);
v_l_3214_ = lean_ctor_get(v_x_3211_, 3);
v_r_3215_ = lean_ctor_get(v_x_3211_, 4);
v___x_3216_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3210_, v_r_3215_);
lean_inc(v_v_3213_);
lean_inc(v_k_3212_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_k_3212_);
lean_ctor_set(v___x_3217_, 1, v_v_3213_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3216_);
v_init_3210_ = v___x_3218_;
v_x_3211_ = v_l_3214_;
goto _start;
}
else
{
return v_init_3210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3220_, v_x_3221_);
lean_dec(v_x_3221_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3223_, size_t v_i_3224_, lean_object* v_bs_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = lean_usize_dec_lt(v_i_3224_, v_sz_3223_);
if (v___x_3226_ == 0)
{
return v_bs_3225_;
}
else
{
lean_object* v_v_3227_; lean_object* v___x_3228_; lean_object* v_bs_x27_3229_; size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v_v_3227_ = lean_array_uget(v_bs_3225_, v_i_3224_);
v___x_3228_ = lean_unsigned_to_nat(0u);
v_bs_x27_3229_ = lean_array_uset(v_bs_3225_, v_i_3224_, v___x_3228_);
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3224_, v___x_3230_);
v___x_3232_ = lean_array_uset(v_bs_x27_3229_, v_i_3224_, v_v_3227_);
v_i_3224_ = v___x_3231_;
v_bs_3225_ = v___x_3232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_bs_3236_){
_start:
{
size_t v_sz_boxed_3237_; size_t v_i_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3237_, v_i_boxed_3238_, v_bs_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3240_){
_start:
{
size_t v_sz_3241_; size_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_sz_3241_ = lean_array_size(v_a_3240_);
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3241_, v___x_3242_, v_a_3240_);
v___x_3244_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3245_){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_array_mk(v_a_3245_);
v___x_3247_ = l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_box(0);
return v___x_3249_;
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3251_; 
v_val_3250_ = lean_ctor_get(v_x_3248_, 0);
lean_inc(v_val_3250_);
lean_dec_ref(v_x_3248_);
v___x_3251_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3250_);
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3252_, size_t v_i_3253_, lean_object* v_bs_3254_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
if (v___x_3255_ == 0)
{
return v_bs_3254_;
}
else
{
lean_object* v_v_3256_; lean_object* v___x_3257_; lean_object* v_bs_x27_3258_; lean_object* v___x_3259_; size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v_v_3256_ = lean_array_uget(v_bs_3254_, v_i_3253_);
v___x_3257_ = lean_unsigned_to_nat(0u);
v_bs_x27_3258_ = lean_array_uset(v_bs_3254_, v_i_3253_, v___x_3257_);
v___x_3259_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3256_);
v___x_3260_ = ((size_t)1ULL);
v___x_3261_ = lean_usize_add(v_i_3253_, v___x_3260_);
v___x_3262_ = lean_array_uset(v_bs_x27_3258_, v_i_3253_, v___x_3259_);
v_i_3253_ = v___x_3261_;
v_bs_3254_ = v___x_3262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_bs_3266_){
_start:
{
size_t v_sz_boxed_3267_; size_t v_i_boxed_3268_; lean_object* v_res_3269_; 
v_sz_boxed_3267_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3268_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3267_, v_i_boxed_3268_, v_bs_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3270_){
_start:
{
size_t v_sz_3271_; size_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_sz_3271_ = lean_array_size(v_a_3270_);
v___x_3272_ = ((size_t)0ULL);
v___x_3273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3271_, v___x_3272_, v_a_3270_);
v___x_3274_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
if (lean_obj_tag(v_a_3275_) == 0)
{
lean_object* v___x_3277_; 
v___x_3277_ = l_List_reverse___redArg(v_a_3276_);
return v___x_3277_;
}
else
{
lean_object* v_head_3278_; lean_object* v_tail_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3289_; 
v_head_3278_ = lean_ctor_get(v_a_3275_, 0);
v_tail_3279_ = lean_ctor_get(v_a_3275_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_a_3275_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3281_ = v_a_3275_;
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_tail_3279_);
lean_inc(v_head_3278_);
lean_dec(v_a_3275_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3283_ = l_Lean_JsonNumber_fromNat(v_head_3278_);
v___x_3284_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v_a_3276_);
lean_ctor_set(v___x_3281_, 0, v___x_3284_);
v___x_3286_ = v___x_3281_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3276_);
v___x_3286_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v_a_3275_ = v_tail_3279_;
v_a_3276_ = v___x_3286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3290_, size_t v_i_3291_, lean_object* v_bs_3292_){
_start:
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_usize_dec_lt(v_i_3291_, v_sz_3290_);
if (v___x_3293_ == 0)
{
return v_bs_3292_;
}
else
{
lean_object* v_v_3294_; lean_object* v_startPosLine_3295_; lean_object* v_startPosCharacter_3296_; lean_object* v_endPosLine_3297_; lean_object* v_endPosCharacter_3298_; lean_object* v___x_3299_; lean_object* v_bs_x27_3300_; lean_object* v___y_3302_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_range_3312_; lean_object* v___x_3313_; 
v_v_3294_ = lean_array_uget(v_bs_3292_, v_i_3291_);
v_startPosLine_3295_ = lean_ctor_get(v_v_3294_, 0);
v_startPosCharacter_3296_ = lean_ctor_get(v_v_3294_, 1);
v_endPosLine_3297_ = lean_ctor_get(v_v_3294_, 2);
v_endPosCharacter_3298_ = lean_ctor_get(v_v_3294_, 3);
v___x_3299_ = lean_unsigned_to_nat(0u);
v_bs_x27_3300_ = lean_array_uset(v_bs_3292_, v_i_3291_, v___x_3299_);
v___x_3307_ = lean_box(0);
lean_inc(v_endPosCharacter_3298_);
v___x_3308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3308_, 0, v_endPosCharacter_3298_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_inc(v_endPosLine_3297_);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_endPosLine_3297_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
lean_inc(v_startPosCharacter_3296_);
v___x_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_startPosCharacter_3296_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
lean_inc(v_startPosLine_3295_);
v___x_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_startPosLine_3295_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v_range_3312_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3311_, v___x_3307_);
v___x_3313_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3294_);
lean_dec(v_v_3294_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = l_List_appendTR___redArg(v_range_3312_, v___x_3307_);
v___y_3302_ = v___x_3314_;
goto v___jp_3301_;
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3324_; 
v_val_3315_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3317_ = v___x_3313_;
v_isShared_3318_ = v_isSharedCheck_3324_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_val_3315_);
lean_dec(v___x_3313_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3324_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set_tag(v___x_3317_, 3);
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_val_3315_);
v___x_3320_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v___x_3307_);
v___x_3322_ = l_List_appendTR___redArg(v_range_3312_, v___x_3321_);
v___y_3302_ = v___x_3322_;
goto v___jp_3301_;
}
}
}
v___jp_3301_:
{
size_t v___x_3303_; size_t v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = ((size_t)1ULL);
v___x_3304_ = lean_usize_add(v_i_3291_, v___x_3303_);
v___x_3305_ = lean_array_uset(v_bs_x27_3300_, v_i_3291_, v___y_3302_);
v_i_3291_ = v___x_3304_;
v_bs_3292_ = v___x_3305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3325_, lean_object* v_i_3326_, lean_object* v_bs_3327_){
_start:
{
size_t v_sz_boxed_3328_; size_t v_i_boxed_3329_; lean_object* v_res_3330_; 
v_sz_boxed_3328_ = lean_unbox_usize(v_sz_3325_);
lean_dec(v_sz_3325_);
v_i_boxed_3329_ = lean_unbox_usize(v_i_3326_);
lean_dec(v_i_3326_);
v_res_3330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3328_, v_i_boxed_3329_, v_bs_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
if (lean_obj_tag(v_a_3331_) == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = l_List_reverse___redArg(v_a_3332_);
return v___x_3333_;
}
else
{
lean_object* v_head_3334_; lean_object* v_snd_3335_; lean_object* v_tail_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3405_; 
v_head_3334_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_head_3334_);
v_snd_3335_ = lean_ctor_get(v_head_3334_, 1);
lean_inc(v_snd_3335_);
v_tail_3336_ = lean_ctor_get(v_a_3331_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_a_3331_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; 
v_unused_3406_ = lean_ctor_get(v_a_3331_, 0);
lean_dec(v_unused_3406_);
v___x_3338_ = v_a_3331_;
v_isShared_3339_ = v_isSharedCheck_3405_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_tail_3336_);
lean_dec(v_a_3331_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3405_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fst_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3403_; 
v_fst_3340_ = lean_ctor_get(v_head_3334_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_head_3334_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v_head_3334_, 1);
lean_dec(v_unused_3404_);
v___x_3342_ = v_head_3334_;
v_isShared_3343_ = v_isSharedCheck_3403_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_fst_3340_);
lean_dec(v_head_3334_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3403_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_definition_x3f_3344_; lean_object* v_usages_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3402_; 
v_definition_x3f_3344_ = lean_ctor_get(v_snd_3335_, 0);
v_usages_3345_ = lean_ctor_get(v_snd_3335_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_snd_3335_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3347_ = v_snd_3335_;
v_isShared_3348_ = v_isSharedCheck_3402_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_usages_3345_);
lean_inc(v_definition_x3f_3344_);
lean_dec(v_snd_3335_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3402_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___y_3353_; lean_object* v___y_3376_; 
v___x_3349_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3340_);
v___x_3350_ = l_Lean_Json_compress(v___x_3349_);
v___x_3351_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3344_) == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_box(0);
v___y_3353_ = v___x_3378_;
goto v___jp_3352_;
}
else
{
lean_object* v_val_3379_; lean_object* v_startPosLine_3380_; lean_object* v_startPosCharacter_3381_; lean_object* v_endPosLine_3382_; lean_object* v_endPosCharacter_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v_range_3389_; lean_object* v___x_3390_; 
v_val_3379_ = lean_ctor_get(v_definition_x3f_3344_, 0);
lean_inc(v_val_3379_);
lean_dec_ref(v_definition_x3f_3344_);
v_startPosLine_3380_ = lean_ctor_get(v_val_3379_, 0);
v_startPosCharacter_3381_ = lean_ctor_get(v_val_3379_, 1);
v_endPosLine_3382_ = lean_ctor_get(v_val_3379_, 2);
v_endPosCharacter_3383_ = lean_ctor_get(v_val_3379_, 3);
v___x_3384_ = lean_box(0);
lean_inc(v_endPosCharacter_3383_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_endPosCharacter_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
lean_inc(v_endPosLine_3382_);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_endPosLine_3382_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_inc(v_startPosCharacter_3381_);
v___x_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_startPosCharacter_3381_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
lean_inc(v_startPosLine_3380_);
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_startPosLine_3380_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v_range_3389_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3388_, v___x_3384_);
v___x_3390_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3379_);
lean_dec(v_val_3379_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = l_List_appendTR___redArg(v_range_3389_, v___x_3384_);
v___y_3376_ = v___x_3391_;
goto v___jp_3375_;
}
else
{
lean_object* v_val_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3401_; 
v_val_3392_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3394_ = v___x_3390_;
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_val_3392_);
lean_dec(v___x_3390_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3401_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 3);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_val_3392_);
v___x_3397_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___x_3384_);
v___x_3399_ = l_List_appendTR___redArg(v_range_3389_, v___x_3398_);
v___y_3376_ = v___x_3399_;
goto v___jp_3375_;
}
}
}
}
v___jp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3353_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v___x_3354_);
lean_ctor_set(v___x_3342_, 0, v___x_3351_);
v___x_3356_ = v___x_3342_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; size_t v_sz_3358_; size_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3357_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3358_ = lean_array_size(v_usages_3345_);
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3358_, v___x_3359_, v_usages_3345_);
v___x_3361_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3360_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v___x_3361_);
lean_ctor_set(v___x_3347_, 0, v___x_3357_);
v___x_3363_ = v___x_3347_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_box(0);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v___x_3364_);
lean_ctor_set(v___x_3338_, 0, v___x_3363_);
v___x_3366_ = v___x_3338_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3356_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = l_Lean_Json_mkObj(v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3350_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v_a_3332_);
v_a_3331_ = v_tail_3336_;
v_a_3332_ = v___x_3370_;
goto _start;
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___y_3376_);
v___y_3353_ = v___x_3377_;
goto v___jp_3352_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
if (lean_obj_tag(v_a_3407_) == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = l_List_reverse___redArg(v_a_3408_);
return v___x_3409_;
}
else
{
lean_object* v_head_3410_; lean_object* v_snd_3411_; lean_object* v_tail_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3464_; 
v_head_3410_ = lean_ctor_get(v_a_3407_, 0);
lean_inc(v_head_3410_);
v_snd_3411_ = lean_ctor_get(v_head_3410_, 1);
lean_inc(v_snd_3411_);
v_tail_3412_ = lean_ctor_get(v_a_3407_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v_a_3407_, 0);
lean_dec(v_unused_3465_);
v___x_3414_ = v_a_3407_;
v_isShared_3415_ = v_isSharedCheck_3464_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_tail_3412_);
lean_dec(v_a_3407_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3464_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v_fst_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3462_; 
v_fst_3416_ = lean_ctor_get(v_head_3410_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_head_3410_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; 
v_unused_3463_ = lean_ctor_get(v_head_3410_, 1);
lean_dec(v_unused_3463_);
v___x_3418_ = v_head_3410_;
v_isShared_3419_ = v_isSharedCheck_3462_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_fst_3416_);
lean_dec(v_head_3410_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3462_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_rangeStartPosLine_3420_; lean_object* v_rangeStartPosCharacter_3421_; lean_object* v_rangeEndPosLine_3422_; lean_object* v_rangeEndPosCharacter_3423_; lean_object* v_selectionRangeStartPosLine_3424_; lean_object* v_selectionRangeStartPosCharacter_3425_; lean_object* v_selectionRangeEndPosLine_3426_; lean_object* v_selectionRangeEndPosCharacter_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v_rangeStartPosLine_3420_ = lean_ctor_get(v_snd_3411_, 0);
lean_inc(v_rangeStartPosLine_3420_);
v_rangeStartPosCharacter_3421_ = lean_ctor_get(v_snd_3411_, 1);
lean_inc(v_rangeStartPosCharacter_3421_);
v_rangeEndPosLine_3422_ = lean_ctor_get(v_snd_3411_, 2);
lean_inc(v_rangeEndPosLine_3422_);
v_rangeEndPosCharacter_3423_ = lean_ctor_get(v_snd_3411_, 3);
lean_inc(v_rangeEndPosCharacter_3423_);
v_selectionRangeStartPosLine_3424_ = lean_ctor_get(v_snd_3411_, 4);
lean_inc(v_selectionRangeStartPosLine_3424_);
v_selectionRangeStartPosCharacter_3425_ = lean_ctor_get(v_snd_3411_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3425_);
v_selectionRangeEndPosLine_3426_ = lean_ctor_get(v_snd_3411_, 6);
lean_inc(v_selectionRangeEndPosLine_3426_);
v_selectionRangeEndPosCharacter_3427_ = lean_ctor_get(v_snd_3411_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3427_);
lean_dec(v_snd_3411_);
v___x_3428_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3420_);
v___x_3429_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
v___x_3430_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3421_);
v___x_3431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
v___x_3432_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3422_);
v___x_3433_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
v___x_3434_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3423_);
v___x_3435_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
v___x_3436_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3424_);
v___x_3437_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
v___x_3438_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3425_);
v___x_3439_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
v___x_3440_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3426_);
v___x_3441_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
v___x_3442_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3427_);
v___x_3443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
v___x_3444_ = lean_unsigned_to_nat(8u);
v___x_3445_ = lean_mk_empty_array_with_capacity(v___x_3444_);
v___x_3446_ = lean_array_push(v___x_3445_, v___x_3429_);
v___x_3447_ = lean_array_push(v___x_3446_, v___x_3431_);
v___x_3448_ = lean_array_push(v___x_3447_, v___x_3433_);
v___x_3449_ = lean_array_push(v___x_3448_, v___x_3435_);
v___x_3450_ = lean_array_push(v___x_3449_, v___x_3437_);
v___x_3451_ = lean_array_push(v___x_3450_, v___x_3439_);
v___x_3452_ = lean_array_push(v___x_3451_, v___x_3441_);
v___x_3453_ = lean_array_push(v___x_3452_, v___x_3443_);
v___x_3454_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v___x_3454_);
v___x_3456_ = v___x_3418_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3416_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v_a_3408_);
lean_ctor_set(v___x_3414_, 0, v___x_3456_);
v___x_3458_ = v___x_3414_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_a_3408_);
v___x_3458_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
v_a_3407_ = v_tail_3412_;
v_a_3408_ = v___x_3458_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3466_, lean_object* v_x_3467_){
_start:
{
if (lean_obj_tag(v_x_3467_) == 0)
{
lean_object* v_k_3468_; lean_object* v_v_3469_; lean_object* v_l_3470_; lean_object* v_r_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_k_3468_ = lean_ctor_get(v_x_3467_, 1);
v_v_3469_ = lean_ctor_get(v_x_3467_, 2);
v_l_3470_ = lean_ctor_get(v_x_3467_, 3);
v_r_3471_ = lean_ctor_get(v_x_3467_, 4);
v___x_3472_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3466_, v_r_3471_);
lean_inc(v_v_3469_);
lean_inc(v_k_3468_);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v_k_3468_);
lean_ctor_set(v___x_3473_, 1, v_v_3469_);
v___x_3474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3472_);
v_init_3466_ = v___x_3474_;
v_x_3467_ = v_l_3470_;
goto _start;
}
else
{
return v_init_3466_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3476_, lean_object* v_x_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3476_, v_x_3477_);
lean_dec(v_x_3477_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3479_){
_start:
{
lean_object* v_version_3480_; lean_object* v_references_3481_; lean_object* v_decls_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_version_3480_ = lean_ctor_get(v_x_3479_, 0);
lean_inc(v_version_3480_);
v_references_3481_ = lean_ctor_get(v_x_3479_, 1);
lean_inc(v_references_3481_);
v_decls_3482_ = lean_ctor_get(v_x_3479_, 2);
lean_inc(v_decls_3482_);
lean_dec_ref(v_x_3479_);
v___x_3483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3484_ = l_Lean_JsonNumber_fromNat(v_version_3480_);
v___x_3485_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3483_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3490_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3487_, v_references_3481_);
lean_dec(v_references_3481_);
v___x_3491_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3490_, v___x_3487_);
v___x_3492_ = l_Lean_Json_mkObj(v___x_3491_);
v___x_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3489_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3487_);
v___x_3495_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3496_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3487_, v_decls_3482_);
lean_dec(v_decls_3482_);
v___x_3497_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3496_, v___x_3487_);
v___x_3498_ = l_Lean_Json_mkObj(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3495_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3487_);
v___x_3501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v___x_3487_);
v___x_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3494_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3488_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3505_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3503_, v___x_3504_);
v___x_3506_ = l_Lean_Json_mkObj(v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3509_, size_t v_i_3510_, lean_object* v_bs_3511_){
_start:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_usize_dec_lt(v_i_3510_, v_sz_3509_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_bs_3511_);
return v___x_3513_;
}
else
{
lean_object* v_v_3514_; lean_object* v___x_3515_; 
v_v_3514_ = lean_array_uget_borrowed(v_bs_3511_, v_i_3510_);
lean_inc(v_v_3514_);
v___x_3515_ = l_Lean_Json_getStr_x3f(v_v_3514_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v_bs_3511_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3525_; lean_object* v_bs_x27_3526_; size_t v___x_3527_; size_t v___x_3528_; lean_object* v___x_3529_; 
v_a_3524_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3515_);
v___x_3525_ = lean_unsigned_to_nat(0u);
v_bs_x27_3526_ = lean_array_uset(v_bs_3511_, v_i_3510_, v___x_3525_);
v___x_3527_ = ((size_t)1ULL);
v___x_3528_ = lean_usize_add(v_i_3510_, v___x_3527_);
v___x_3529_ = lean_array_uset(v_bs_x27_3526_, v_i_3510_, v_a_3524_);
v_i_3510_ = v___x_3528_;
v_bs_3511_ = v___x_3529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3531_, lean_object* v_i_3532_, lean_object* v_bs_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v_i_boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3531_);
lean_dec(v_sz_3531_);
v_i_boxed_3535_ = lean_unbox_usize(v_i_3532_);
lean_dec(v_i_3532_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3534_, v_i_boxed_3535_, v_bs_3533_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3537_){
_start:
{
if (lean_obj_tag(v_x_3537_) == 4)
{
lean_object* v_elems_3538_; size_t v_sz_3539_; size_t v___x_3540_; lean_object* v___x_3541_; 
v_elems_3538_ = lean_ctor_get(v_x_3537_, 0);
lean_inc_ref(v_elems_3538_);
lean_dec_ref(v_x_3537_);
v_sz_3539_ = lean_array_size(v_elems_3538_);
v___x_3540_ = ((size_t)0ULL);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3539_, v___x_3540_, v_elems_3538_);
return v___x_3541_;
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3542_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3543_ = lean_unsigned_to_nat(80u);
v___x_3544_ = l_Lean_Json_pretty(v_x_3537_, v___x_3543_);
v___x_3545_ = lean_string_append(v___x_3542_, v___x_3544_);
lean_dec_ref(v___x_3544_);
v___x_3546_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3547_ = lean_string_append(v___x_3545_, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3549_, lean_object* v_k_3550_){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = l_Lean_Json_getObjValD(v_j_3549_, v_k_3550_);
v___x_3552_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3553_, lean_object* v_k_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3553_, v_k_3554_);
lean_dec_ref(v_k_3554_);
return v_res_3555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = 1;
v___x_3563_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3567_ = lean_string_append(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = 1;
v___x_3571_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3574_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3575_ = lean_string_append(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3577_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3578_ = lean_string_append(v___x_3577_, v___x_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3579_, v___x_3580_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3591_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3587_ = lean_string_append(v___x_3586_, v_a_3582_);
lean_dec(v_a_3582_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3587_);
v___x_3589_ = v___x_3584_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_a_3592_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3581_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3581_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 0);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
v_a_3600_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3581_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3581_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3610_, size_t v_i_3611_, lean_object* v_bs_3612_){
_start:
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_usize_dec_lt(v_i_3611_, v_sz_3610_);
if (v___x_3613_ == 0)
{
return v_bs_3612_;
}
else
{
lean_object* v_v_3614_; lean_object* v___x_3615_; lean_object* v_bs_x27_3616_; lean_object* v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
v_v_3614_ = lean_array_uget(v_bs_3612_, v_i_3611_);
v___x_3615_ = lean_unsigned_to_nat(0u);
v_bs_x27_3616_ = lean_array_uset(v_bs_3612_, v_i_3611_, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3617_, 0, v_v_3614_);
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3611_, v___x_3618_);
v___x_3620_ = lean_array_uset(v_bs_x27_3616_, v_i_3611_, v___x_3617_);
v_i_3611_ = v___x_3619_;
v_bs_3612_ = v___x_3620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3622_, lean_object* v_i_3623_, lean_object* v_bs_3624_){
_start:
{
size_t v_sz_boxed_3625_; size_t v_i_boxed_3626_; lean_object* v_res_3627_; 
v_sz_boxed_3625_ = lean_unbox_usize(v_sz_3622_);
lean_dec(v_sz_3622_);
v_i_boxed_3626_ = lean_unbox_usize(v_i_3623_);
lean_dec(v_i_3623_);
v_res_3627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3625_, v_i_boxed_3626_, v_bs_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3628_){
_start:
{
size_t v_sz_3629_; size_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_sz_3629_ = lean_array_size(v_a_3628_);
v___x_3630_ = ((size_t)0ULL);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3629_, v___x_3630_, v_a_3628_);
v___x_3632_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3634_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3635_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3633_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_box(0);
v___x_3638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3637_);
v___x_3640_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3641_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3639_, v___x_3640_);
v___x_3642_ = l_Lean_Json_mkObj(v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3645_, lean_object* v_k_3646_){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = l_Lean_Json_getObjValD(v_j_3645_, v_k_3646_);
v___x_3648_ = l_Lean_Json_getStr_x3f(v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3649_, lean_object* v_k_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3649_, v_k_3650_);
lean_dec_ref(v_k_3650_);
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = 1;
v___x_3659_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3659_, v___x_3658_);
return v___x_3660_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3663_ = lean_string_append(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = 1;
v___x_3667_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3667_, v___x_3666_);
return v___x_3668_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3670_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3671_ = lean_string_append(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3674_ = lean_string_append(v___x_3673_, v___x_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3675_){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3677_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3675_, v___x_3676_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3687_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3687_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3687_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3683_ = lean_string_append(v___x_3682_, v_a_3678_);
lean_dec(v_a_3678_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3683_);
v___x_3685_ = v___x_3680_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
v_a_3688_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3677_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3677_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set_tag(v___x_3690_, 0);
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
v_a_3696_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3677_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3677_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3706_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3707_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3708_, 0, v_x_3706_);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_box(0);
v___x_3711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
lean_ctor_set(v___x_3712_, 1, v___x_3710_);
v___x_3713_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3714_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3712_, v___x_3713_);
v___x_3715_ = l_Lean_Json_mkObj(v___x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_unsigned_to_nat(0u);
return v___x_3719_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_unsigned_to_nat(1u);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3721_);
lean_dec_ref(v_x_3721_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3723_, lean_object* v_k_3724_){
_start:
{
if (lean_obj_tag(v_t_3723_) == 0)
{
lean_object* v_namespace_3725_; lean_object* v_exceptions_3726_; lean_object* v___x_3727_; 
v_namespace_3725_ = lean_ctor_get(v_t_3723_, 0);
lean_inc(v_namespace_3725_);
v_exceptions_3726_ = lean_ctor_get(v_t_3723_, 1);
lean_inc_ref(v_exceptions_3726_);
lean_dec_ref(v_t_3723_);
v___x_3727_ = lean_apply_2(v_k_3724_, v_namespace_3725_, v_exceptions_3726_);
return v___x_3727_;
}
else
{
lean_object* v_from_3728_; lean_object* v_to_3729_; lean_object* v___x_3730_; 
v_from_3728_ = lean_ctor_get(v_t_3723_, 0);
lean_inc(v_from_3728_);
v_to_3729_ = lean_ctor_get(v_t_3723_, 1);
lean_inc(v_to_3729_);
lean_dec_ref(v_t_3723_);
v___x_3730_ = lean_apply_2(v_k_3724_, v_from_3728_, v_to_3729_);
return v___x_3730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3731_, lean_object* v_ctorIdx_3732_, lean_object* v_t_3733_, lean_object* v_h_3734_, lean_object* v_k_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3733_, v_k_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3737_, lean_object* v_ctorIdx_3738_, lean_object* v_t_3739_, lean_object* v_h_3740_, lean_object* v_k_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3737_, v_ctorIdx_3738_, v_t_3739_, v_h_3740_, v_k_3741_);
lean_dec(v_ctorIdx_3738_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3743_, lean_object* v_allExcept_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3743_, v_allExcept_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3746_, lean_object* v_t_3747_, lean_object* v_h_3748_, lean_object* v_allExcept_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3747_, v_allExcept_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3751_, lean_object* v_renamed_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3751_, v_renamed_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3754_, lean_object* v_t_3755_, lean_object* v_h_3756_, lean_object* v_renamed_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3755_, v_renamed_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3759_, size_t v_i_3760_, lean_object* v_bs_3761_){
_start:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_usize_dec_lt(v_i_3760_, v_sz_3759_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_bs_3761_);
return v___x_3763_;
}
else
{
lean_object* v_v_3764_; lean_object* v___x_3765_; 
v_v_3764_ = lean_array_uget_borrowed(v_bs_3761_, v_i_3760_);
lean_inc(v_v_3764_);
v___x_3765_ = l_Lean_Name_fromJson_x3f(v_v_3764_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec_ref(v_bs_3761_);
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v_bs_x27_3776_; size_t v___x_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
v_a_3774_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3774_);
lean_dec_ref(v___x_3765_);
v___x_3775_ = lean_unsigned_to_nat(0u);
v_bs_x27_3776_ = lean_array_uset(v_bs_3761_, v_i_3760_, v___x_3775_);
v___x_3777_ = ((size_t)1ULL);
v___x_3778_ = lean_usize_add(v_i_3760_, v___x_3777_);
v___x_3779_ = lean_array_uset(v_bs_x27_3776_, v_i_3760_, v_a_3774_);
v_i_3760_ = v___x_3778_;
v_bs_3761_ = v___x_3779_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3781_, lean_object* v_i_3782_, lean_object* v_bs_3783_){
_start:
{
size_t v_sz_boxed_3784_; size_t v_i_boxed_3785_; lean_object* v_res_3786_; 
v_sz_boxed_3784_ = lean_unbox_usize(v_sz_3781_);
lean_dec(v_sz_3781_);
v_i_boxed_3785_ = lean_unbox_usize(v_i_3782_);
lean_dec(v_i_3782_);
v_res_3786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3784_, v_i_boxed_3785_, v_bs_3783_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3787_){
_start:
{
if (lean_obj_tag(v_x_3787_) == 4)
{
lean_object* v_elems_3788_; size_t v_sz_3789_; size_t v___x_3790_; lean_object* v___x_3791_; 
v_elems_3788_ = lean_ctor_get(v_x_3787_, 0);
lean_inc_ref(v_elems_3788_);
lean_dec_ref(v_x_3787_);
v_sz_3789_ = lean_array_size(v_elems_3788_);
v___x_3790_ = ((size_t)0ULL);
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3789_, v___x_3790_, v_elems_3788_);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3792_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3793_ = lean_unsigned_to_nat(80u);
v___x_3794_ = l_Lean_Json_pretty(v_x_3787_, v___x_3793_);
v___x_3795_ = lean_string_append(v___x_3792_, v___x_3794_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3797_ = lean_string_append(v___x_3795_, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
return v___x_3798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3833_){
_start:
{
lean_object* v___x_3834_; 
lean_inc(v_json_3833_);
v___x_3834_ = l_Lean_Json_getTag_x3f(v_json_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3835_; 
lean_dec(v_json_3833_);
v___x_3835_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3835_;
}
else
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_val_3836_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_val_3836_);
lean_dec_ref(v___x_3834_);
v___x_3837_ = lean_box(0);
v___x_3838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3839_ = lean_string_dec_eq(v_val_3836_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3840_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3841_ = lean_string_dec_eq(v_val_3836_, v___x_3840_);
lean_dec(v_val_3836_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; 
lean_dec(v_json_3833_);
v___x_3842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3842_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_unsigned_to_nat(2u);
v___x_3844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3845_ = l_Lean_Json_parseCtorFields(v_json_3833_, v___x_3840_, v___x_3843_, v___x_3844_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_a_3854_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3845_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_array_get_borrowed(v___x_3837_, v_a_3854_, v___x_3855_);
lean_inc(v___x_3856_);
v___x_3857_ = l_Lean_Name_fromJson_x3f(v___x_3856_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_a_3854_);
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_a_3866_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3857_);
v___x_3867_ = lean_unsigned_to_nat(1u);
v___x_3868_ = lean_array_get(v___x_3837_, v_a_3854_, v___x_3867_);
lean_dec(v_a_3854_);
v___x_3869_ = l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3868_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3866_);
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
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3886_; 
v_a_3878_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3880_ = v___x_3869_;
v_isShared_3881_ = v_isSharedCheck_3886_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3869_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3886_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v_a_3866_);
lean_ctor_set(v___x_3882_, 1, v_a_3878_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v___x_3882_);
v___x_3884_ = v___x_3880_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_dec(v_val_3836_);
v___x_3887_ = lean_unsigned_to_nat(2u);
v___x_3888_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3889_ = l_Lean_Json_parseCtorFields(v_json_3833_, v___x_3838_, v___x_3887_, v___x_3888_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_a_3898_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3889_);
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_array_get_borrowed(v___x_3837_, v_a_3898_, v___x_3899_);
lean_inc(v___x_3900_);
v___x_3901_ = l_Lean_Name_fromJson_x3f(v___x_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_a_3898_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3910_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3901_);
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_array_get(v___x_3837_, v_a_3898_, v___x_3911_);
lean_dec(v_a_3898_);
v___x_3913_ = l_Lean_Name_fromJson_x3f(v___x_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_a_3910_);
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
v_a_3922_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3924_ = v___x_3913_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3913_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v_a_3910_);
lean_ctor_set(v___x_3926_, 1, v_a_3922_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3933_, size_t v_i_3934_, lean_object* v_bs_3935_){
_start:
{
uint8_t v___x_3936_; 
v___x_3936_ = lean_usize_dec_lt(v_i_3934_, v_sz_3933_);
if (v___x_3936_ == 0)
{
return v_bs_3935_;
}
else
{
lean_object* v_v_3937_; lean_object* v___x_3938_; lean_object* v_bs_x27_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
v_v_3937_ = lean_array_uget(v_bs_3935_, v_i_3934_);
v___x_3938_ = lean_unsigned_to_nat(0u);
v_bs_x27_3939_ = lean_array_uset(v_bs_3935_, v_i_3934_, v___x_3938_);
v___x_3940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3937_, v___x_3936_);
v___x_3941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_i_3934_, v___x_3942_);
v___x_3944_ = lean_array_uset(v_bs_x27_3939_, v_i_3934_, v___x_3941_);
v_i_3934_ = v___x_3943_;
v_bs_3935_ = v___x_3944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_bs_3948_){
_start:
{
size_t v_sz_boxed_3949_; size_t v_i_boxed_3950_; lean_object* v_res_3951_; 
v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3950_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3949_, v_i_boxed_3950_, v_bs_3948_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3952_){
_start:
{
size_t v_sz_3953_; size_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_sz_3953_ = lean_array_size(v_a_3952_);
v___x_3954_ = ((size_t)0ULL);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3953_, v___x_3954_, v_a_3952_);
v___x_3956_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3957_){
_start:
{
if (lean_obj_tag(v_x_3957_) == 0)
{
lean_object* v_namespace_3958_; lean_object* v_exceptions_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3981_; 
v_namespace_3958_ = lean_ctor_get(v_x_3957_, 0);
v_exceptions_3959_ = lean_ctor_get(v_x_3957_, 1);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_x_3957_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3961_ = v_x_3957_;
v_isShared_3962_ = v_isSharedCheck_3981_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_exceptions_3959_);
lean_inc(v_namespace_3958_);
lean_dec(v_x_3957_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3981_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3964_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3965_ = 1;
v___x_3966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3958_, v___x_3965_);
v___x_3967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3967_);
lean_ctor_set(v___x_3961_, 0, v___x_3964_);
v___x_3969_ = v___x_3961_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3964_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3970_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3971_ = l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3959_);
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3970_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = lean_box(0);
v___x_3974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3969_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = l_Lean_Json_mkObj(v___x_3975_);
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3963_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
lean_ctor_set(v___x_3978_, 1, v___x_3973_);
v___x_3979_ = l_Lean_Json_mkObj(v___x_3978_);
return v___x_3979_;
}
}
}
else
{
lean_object* v_from_3982_; lean_object* v_to_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4006_; 
v_from_3982_ = lean_ctor_get(v_x_3957_, 0);
v_to_3983_ = lean_ctor_get(v_x_3957_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_x_3957_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3985_ = v_x_3957_;
v_isShared_3986_ = v_isSharedCheck_4006_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_to_3983_);
lean_inc(v_from_3982_);
lean_dec(v_x_3957_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4006_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3988_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3989_ = 1;
v___x_3990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3982_, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set_tag(v___x_3985_, 0);
lean_ctor_set(v___x_3985_, 1, v___x_3991_);
lean_ctor_set(v___x_3985_, 0, v___x_3988_);
v___x_3993_ = v___x_3985_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3994_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3983_, v___x_3989_);
v___x_3996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3994_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3993_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = l_Lean_Json_mkObj(v___x_4000_);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_3987_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_3998_);
v___x_4004_ = l_Lean_Json_mkObj(v___x_4003_);
return v___x_4004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_bs_4011_){
_start:
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4013_, 0, v_bs_4011_);
return v___x_4013_;
}
else
{
lean_object* v_v_4014_; lean_object* v___x_4015_; 
v_v_4014_ = lean_array_uget_borrowed(v_bs_4011_, v_i_4010_);
lean_inc(v_v_4014_);
v___x_4015_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_4014_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_bs_4011_);
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v_bs_x27_4026_; size_t v___x_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v_a_4024_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4015_);
v___x_4025_ = lean_unsigned_to_nat(0u);
v_bs_x27_4026_ = lean_array_uset(v_bs_4011_, v_i_4010_, v___x_4025_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_add(v_i_4010_, v___x_4027_);
v___x_4029_ = lean_array_uset(v_bs_x27_4026_, v_i_4010_, v_a_4024_);
v_i_4010_ = v___x_4028_;
v_bs_4011_ = v___x_4029_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4031_, lean_object* v_i_4032_, lean_object* v_bs_4033_){
_start:
{
size_t v_sz_boxed_4034_; size_t v_i_boxed_4035_; lean_object* v_res_4036_; 
v_sz_boxed_4034_ = lean_unbox_usize(v_sz_4031_);
lean_dec(v_sz_4031_);
v_i_boxed_4035_ = lean_unbox_usize(v_i_4032_);
lean_dec(v_i_4032_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4034_, v_i_boxed_4035_, v_bs_4033_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_4037_){
_start:
{
if (lean_obj_tag(v_x_4037_) == 4)
{
lean_object* v_elems_4038_; size_t v_sz_4039_; size_t v___x_4040_; lean_object* v___x_4041_; 
v_elems_4038_ = lean_ctor_get(v_x_4037_, 0);
lean_inc_ref(v_elems_4038_);
lean_dec_ref(v_x_4037_);
v_sz_4039_ = lean_array_size(v_elems_4038_);
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_4039_, v___x_4040_, v_elems_4038_);
return v___x_4041_;
}
else
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4042_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4043_ = lean_unsigned_to_nat(80u);
v___x_4044_ = l_Lean_Json_pretty(v_x_4037_, v___x_4043_);
v___x_4045_ = lean_string_append(v___x_4042_, v___x_4044_);
lean_dec_ref(v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4047_ = lean_string_append(v___x_4045_, v___x_4046_);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_4049_, lean_object* v_k_4050_){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = l_Lean_Json_getObjValD(v_j_4049_, v_k_4050_);
v___x_4052_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_4053_, lean_object* v_k_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_4053_, v_k_4054_);
lean_dec_ref(v_k_4054_);
return v_res_4055_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = 1;
v___x_4063_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4064_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4063_, v___x_4062_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4066_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4067_ = lean_string_append(v___x_4066_, v___x_4065_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = 1;
v___x_4071_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4072_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4071_, v___x_4070_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4074_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4075_ = lean_string_append(v___x_4074_, v___x_4073_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4077_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4078_ = lean_string_append(v___x_4077_, v___x_4076_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = 1;
v___x_4083_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4083_, v___x_4082_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4086_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4087_ = lean_string_append(v___x_4086_, v___x_4085_);
return v___x_4087_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4089_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4090_ = lean_string_append(v___x_4089_, v___x_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4091_){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4091_);
v___x_4093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4091_, v___x_4092_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_json_4091_);
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4096_ = v___x_4093_;
v_isShared_4097_ = v_isSharedCheck_4103_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4103_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4099_ = lean_string_append(v___x_4098_, v_a_4094_);
lean_dec(v_a_4094_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4099_);
v___x_4101_ = v___x_4096_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
else
{
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_json_4091_);
v_a_4104_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4093_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4093_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
lean_ctor_set_tag(v___x_4106_, 0);
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v_a_4112_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4112_);
lean_dec_ref(v___x_4093_);
v___x_4113_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4114_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4091_, v___x_4113_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_a_4112_);
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
v___x_4119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
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
lean_dec(v_a_4112_);
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
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4141_; 
v_a_4133_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4135_ = v___x_4114_;
v_isShared_4136_ = v_isSharedCheck_4141_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4114_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4141_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v_a_4112_);
lean_ctor_set(v___x_4137_, 1, v_a_4133_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4137_);
v___x_4139_ = v___x_4135_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4144_, size_t v_i_4145_, lean_object* v_bs_4146_){
_start:
{
uint8_t v___x_4147_; 
v___x_4147_ = lean_usize_dec_lt(v_i_4145_, v_sz_4144_);
if (v___x_4147_ == 0)
{
return v_bs_4146_;
}
else
{
lean_object* v_v_4148_; lean_object* v___x_4149_; lean_object* v_bs_x27_4150_; lean_object* v___x_4151_; size_t v___x_4152_; size_t v___x_4153_; lean_object* v___x_4154_; 
v_v_4148_ = lean_array_uget(v_bs_4146_, v_i_4145_);
v___x_4149_ = lean_unsigned_to_nat(0u);
v_bs_x27_4150_ = lean_array_uset(v_bs_4146_, v_i_4145_, v___x_4149_);
v___x_4151_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4148_);
v___x_4152_ = ((size_t)1ULL);
v___x_4153_ = lean_usize_add(v_i_4145_, v___x_4152_);
v___x_4154_ = lean_array_uset(v_bs_x27_4150_, v_i_4145_, v___x_4151_);
v_i_4145_ = v___x_4153_;
v_bs_4146_ = v___x_4154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4156_, lean_object* v_i_4157_, lean_object* v_bs_4158_){
_start:
{
size_t v_sz_boxed_4159_; size_t v_i_boxed_4160_; lean_object* v_res_4161_; 
v_sz_boxed_4159_ = lean_unbox_usize(v_sz_4156_);
lean_dec(v_sz_4156_);
v_i_boxed_4160_ = lean_unbox_usize(v_i_4157_);
lean_dec(v_i_4157_);
v_res_4161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4159_, v_i_boxed_4160_, v_bs_4158_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4162_){
_start:
{
size_t v_sz_4163_; size_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_sz_4163_ = lean_array_size(v_a_4162_);
v___x_4164_ = ((size_t)0ULL);
v___x_4165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4163_, v___x_4164_, v_a_4162_);
v___x_4166_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4167_){
_start:
{
lean_object* v_identifier_4168_; lean_object* v_openNamespaces_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4189_; 
v_identifier_4168_ = lean_ctor_get(v_x_4167_, 0);
v_openNamespaces_4169_ = lean_ctor_get(v_x_4167_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_x_4167_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4171_ = v_x_4167_;
v_isShared_4172_ = v_isSharedCheck_4189_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_openNamespaces_4169_);
lean_inc(v_identifier_4168_);
lean_dec(v_x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4189_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4174_, 0, v_identifier_4168_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 1, v___x_4174_);
lean_ctor_set(v___x_4171_, 0, v___x_4173_);
v___x_4176_ = v___x_4171_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4176_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
v___x_4179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4180_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4169_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___x_4177_);
v___x_4183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4177_);
v___x_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4178_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4186_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4184_, v___x_4185_);
v___x_4187_ = l_Lean_Json_mkObj(v___x_4186_);
return v___x_4187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4195_, lean_object* v_k_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Json_getObjValD(v_j_4195_, v_k_4196_);
switch(lean_obj_tag(v___x_4197_))
{
case 3:
{
lean_object* v_s_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4206_; 
v_s_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4206_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_s_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4206_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 0);
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_s_4198_);
v___x_4203_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
case 2:
{
lean_object* v_n_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4215_; 
v_n_4207_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4209_ = v___x_4197_;
v_isShared_4210_ = v_isSharedCheck_4215_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_n_4207_);
lean_dec(v___x_4197_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4215_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 1);
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_n_4207_);
v___x_4212_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; 
v___x_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
return v___x_4213_;
}
}
}
default: 
{
lean_object* v___x_4216_; 
lean_dec(v___x_4197_);
v___x_4216_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4217_, lean_object* v_k_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4217_, v_k_4218_);
lean_dec_ref(v_k_4218_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_bs_4222_){
_start:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_bs_4222_);
return v___x_4224_;
}
else
{
lean_object* v_v_4225_; lean_object* v___x_4226_; 
v_v_4225_ = lean_array_uget_borrowed(v_bs_4222_, v_i_4221_);
lean_inc(v_v_4225_);
v___x_4226_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4225_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v_bs_4222_);
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4226_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4236_; lean_object* v_bs_x27_4237_; size_t v___x_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
v_a_4235_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4235_);
lean_dec_ref(v___x_4226_);
v___x_4236_ = lean_unsigned_to_nat(0u);
v_bs_x27_4237_ = lean_array_uset(v_bs_4222_, v_i_4221_, v___x_4236_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_i_4221_, v___x_4238_);
v___x_4240_ = lean_array_uset(v_bs_x27_4237_, v_i_4221_, v_a_4235_);
v_i_4221_ = v___x_4239_;
v_bs_4222_ = v___x_4240_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4242_, lean_object* v_i_4243_, lean_object* v_bs_4244_){
_start:
{
size_t v_sz_boxed_4245_; size_t v_i_boxed_4246_; lean_object* v_res_4247_; 
v_sz_boxed_4245_ = lean_unbox_usize(v_sz_4242_);
lean_dec(v_sz_4242_);
v_i_boxed_4246_ = lean_unbox_usize(v_i_4243_);
lean_dec(v_i_4243_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4245_, v_i_boxed_4246_, v_bs_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4248_){
_start:
{
if (lean_obj_tag(v_x_4248_) == 4)
{
lean_object* v_elems_4249_; size_t v_sz_4250_; size_t v___x_4251_; lean_object* v___x_4252_; 
v_elems_4249_ = lean_ctor_get(v_x_4248_, 0);
lean_inc_ref(v_elems_4249_);
lean_dec_ref(v_x_4248_);
v_sz_4250_ = lean_array_size(v_elems_4249_);
v___x_4251_ = ((size_t)0ULL);
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4250_, v___x_4251_, v_elems_4249_);
return v___x_4252_;
}
else
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4253_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4254_ = lean_unsigned_to_nat(80u);
v___x_4255_ = l_Lean_Json_pretty(v_x_4248_, v___x_4254_);
v___x_4256_ = lean_string_append(v___x_4253_, v___x_4255_);
lean_dec_ref(v___x_4255_);
v___x_4257_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4258_ = lean_string_append(v___x_4256_, v___x_4257_);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
return v___x_4259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4260_, lean_object* v_k_4261_){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = l_Lean_Json_getObjValD(v_j_4260_, v_k_4261_);
v___x_4263_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4264_, lean_object* v_k_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4264_, v_k_4265_);
lean_dec_ref(v_k_4265_);
return v_res_4266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4273_ = 1;
v___x_4274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4274_, v___x_4273_);
return v___x_4275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4278_ = lean_string_append(v___x_4277_, v___x_4276_);
return v___x_4278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4281_ = 1;
v___x_4282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4282_, v___x_4281_);
return v___x_4283_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4284_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4285_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4286_ = lean_string_append(v___x_4285_, v___x_4284_);
return v___x_4286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4287_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4288_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4289_ = lean_string_append(v___x_4288_, v___x_4287_);
return v___x_4289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = 1;
v___x_4294_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4294_, v___x_4293_);
return v___x_4295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4297_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4298_ = lean_string_append(v___x_4297_, v___x_4296_);
return v___x_4298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4300_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4301_ = lean_string_append(v___x_4300_, v___x_4299_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4302_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4302_);
v___x_4304_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4302_, v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4314_; 
lean_dec(v_json_4302_);
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4307_ = v___x_4304_;
v_isShared_4308_ = v_isSharedCheck_4314_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4314_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4310_ = lean_string_append(v___x_4309_, v_a_4305_);
lean_dec(v_a_4305_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 0, v___x_4310_);
v___x_4312_ = v___x_4307_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v___x_4310_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
else
{
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_json_4302_);
v_a_4315_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4304_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4304_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set_tag(v___x_4317_, 0);
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_a_4323_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4304_);
v___x_4324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4302_, v___x_4324_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_a_4323_);
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
v___x_4330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
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
lean_dec(v_a_4323_);
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
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4352_; 
v_a_4344_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4346_ = v___x_4325_;
v_isShared_4347_ = v_isSharedCheck_4352_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4325_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4352_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v_a_4323_);
lean_ctor_set(v___x_4348_, 1, v_a_4344_);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4348_);
v___x_4350_ = v___x_4346_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_bs_4357_){
_start:
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_usize_dec_lt(v_i_4356_, v_sz_4355_);
if (v___x_4358_ == 0)
{
return v_bs_4357_;
}
else
{
lean_object* v_v_4359_; lean_object* v___x_4360_; lean_object* v_bs_x27_4361_; lean_object* v___x_4362_; size_t v___x_4363_; size_t v___x_4364_; lean_object* v___x_4365_; 
v_v_4359_ = lean_array_uget(v_bs_4357_, v_i_4356_);
v___x_4360_ = lean_unsigned_to_nat(0u);
v_bs_x27_4361_ = lean_array_uset(v_bs_4357_, v_i_4356_, v___x_4360_);
v___x_4362_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4359_);
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4356_, v___x_4363_);
v___x_4365_ = lean_array_uset(v_bs_x27_4361_, v_i_4356_, v___x_4362_);
v_i_4356_ = v___x_4364_;
v_bs_4357_ = v___x_4365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4367_, lean_object* v_i_4368_, lean_object* v_bs_4369_){
_start:
{
size_t v_sz_boxed_4370_; size_t v_i_boxed_4371_; lean_object* v_res_4372_; 
v_sz_boxed_4370_ = lean_unbox_usize(v_sz_4367_);
lean_dec(v_sz_4367_);
v_i_boxed_4371_ = lean_unbox_usize(v_i_4368_);
lean_dec(v_i_4368_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4370_, v_i_boxed_4371_, v_bs_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4373_){
_start:
{
size_t v_sz_4374_; size_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_sz_4374_ = lean_array_size(v_a_4373_);
v___x_4375_ = ((size_t)0ULL);
v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4374_, v___x_4375_, v_a_4373_);
v___x_4377_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4378_){
_start:
{
lean_object* v_sourceRequestID_4379_; lean_object* v_queries_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4418_; 
v_sourceRequestID_4379_ = lean_ctor_get(v_x_4378_, 0);
v_queries_4380_ = lean_ctor_get(v_x_4378_, 1);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_x_4378_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4382_ = v_x_4378_;
v_isShared_4383_ = v_isSharedCheck_4418_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_queries_4380_);
lean_inc(v_sourceRequestID_4379_);
lean_dec(v_x_4378_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4418_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___y_4386_; 
v___x_4384_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4379_))
{
case 0:
{
lean_object* v_s_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
v_s_4401_ = lean_ctor_get(v_sourceRequestID_4379_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_sourceRequestID_4379_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v_sourceRequestID_4379_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_s_4401_);
lean_dec(v_sourceRequestID_4379_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 3);
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_s_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
v___y_4386_ = v___x_4406_;
goto v___jp_4385_;
}
}
}
case 1:
{
lean_object* v_n_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
v_n_4409_ = lean_ctor_get(v_sourceRequestID_4379_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v_sourceRequestID_4379_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v_sourceRequestID_4379_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_n_4409_);
lean_dec(v_sourceRequestID_4379_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 2);
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_n_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
v___y_4386_ = v___x_4414_;
goto v___jp_4385_;
}
}
}
default: 
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_box(0);
v___y_4386_ = v___x_4417_;
goto v___jp_4385_;
}
}
v___jp_4385_:
{
lean_object* v___x_4388_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 1, v___y_4386_);
lean_ctor_set(v___x_4382_, 0, v___x_4384_);
v___x_4388_ = v___x_4382_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v___y_4386_);
v___x_4388_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4389_ = lean_box(0);
v___x_4390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4392_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4380_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
lean_ctor_set(v___x_4394_, 1, v___x_4389_);
v___x_4395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v___x_4389_);
v___x_4396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4390_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4398_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4396_, v___x_4397_);
v___x_4399_ = l_Lean_Json_mkObj(v___x_4398_);
return v___x_4399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4421_, lean_object* v_k_4422_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = l_Lean_Json_getObjValD(v_j_4421_, v_k_4422_);
v___x_4424_ = l_Lean_Name_fromJson_x3f(v___x_4423_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4425_, lean_object* v_k_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4425_, v_k_4426_);
lean_dec_ref(v_k_4426_);
return v_res_4427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = 1;
v___x_4435_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4436_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4435_, v___x_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4438_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4439_ = lean_string_append(v___x_4438_, v___x_4437_);
return v___x_4439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = 1;
v___x_4443_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4443_, v___x_4442_);
return v___x_4444_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4445_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4446_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4447_ = lean_string_append(v___x_4446_, v___x_4445_);
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4450_ = lean_string_append(v___x_4449_, v___x_4448_);
return v___x_4450_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = 1;
v___x_4455_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4456_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4455_, v___x_4454_);
return v___x_4456_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4459_ = lean_string_append(v___x_4458_, v___x_4457_);
return v___x_4459_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4460_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4461_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4462_ = lean_string_append(v___x_4461_, v___x_4460_);
return v___x_4462_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = 1;
v___x_4467_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4468_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4467_, v___x_4466_);
return v___x_4468_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4470_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4471_ = lean_string_append(v___x_4470_, v___x_4469_);
return v___x_4471_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4473_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4474_ = lean_string_append(v___x_4473_, v___x_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4475_){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4475_);
v___x_4477_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4475_, v___x_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4487_; 
lean_dec(v_json_4475_);
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4487_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4487_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4483_ = lean_string_append(v___x_4482_, v_a_4478_);
lean_dec(v_a_4478_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4483_);
v___x_4485_ = v___x_4480_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
else
{
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_json_4475_);
v_a_4488_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4477_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4477_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 0);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v_a_4496_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4496_);
lean_dec_ref(v___x_4477_);
v___x_4497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4475_);
v___x_4498_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4475_, v___x_4497_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_a_4496_);
lean_dec(v_json_4475_);
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
v___x_4503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
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
lean_dec(v_a_4496_);
lean_dec(v_json_4475_);
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
lean_dec_ref(v___x_4498_);
v___x_4518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4519_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4475_, v___x_4518_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4529_; 
lean_dec(v_a_4517_);
lean_dec(v_a_4496_);
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
v___x_4524_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
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
lean_dec(v_a_4496_);
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
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4547_; 
v_a_4538_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4540_ = v___x_4519_;
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4519_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4547_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4542_; uint8_t v___x_4543_; lean_object* v___x_4545_; 
v___x_4542_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4542_, 0, v_a_4496_);
lean_ctor_set(v___x_4542_, 1, v_a_4517_);
v___x_4543_ = lean_unbox(v_a_4538_);
lean_dec(v_a_4538_);
lean_ctor_set_uint8(v___x_4542_, sizeof(void*)*2, v___x_4543_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4542_);
v___x_4545_ = v___x_4540_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4542_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4550_){
_start:
{
lean_object* v_module_4551_; lean_object* v_decl_4552_; uint8_t v_isExactMatch_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_module_4551_ = lean_ctor_get(v_x_4550_, 0);
lean_inc(v_module_4551_);
v_decl_4552_ = lean_ctor_get(v_x_4550_, 1);
lean_inc(v_decl_4552_);
v_isExactMatch_4553_ = lean_ctor_get_uint8(v_x_4550_, sizeof(void*)*2);
lean_dec_ref(v_x_4550_);
v___x_4554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4555_ = 1;
v___x_4556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4551_, v___x_4555_);
v___x_4557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4554_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = lean_box(0);
v___x_4560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4552_, v___x_4555_);
v___x_4563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4561_);
lean_ctor_set(v___x_4564_, 1, v___x_4563_);
v___x_4565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
lean_ctor_set(v___x_4565_, 1, v___x_4559_);
v___x_4566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4567_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4567_, 0, v_isExactMatch_4553_);
v___x_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4566_);
lean_ctor_set(v___x_4568_, 1, v___x_4567_);
v___x_4569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
lean_ctor_set(v___x_4569_, 1, v___x_4559_);
v___x_4570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
lean_ctor_set(v___x_4570_, 1, v___x_4559_);
v___x_4571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4565_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4560_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
v___x_4573_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4574_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4572_, v___x_4573_);
v___x_4575_ = l_Lean_Json_mkObj(v___x_4574_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4578_, size_t v_i_4579_, lean_object* v_bs_4580_){
_start:
{
uint8_t v___x_4581_; 
v___x_4581_ = lean_usize_dec_lt(v_i_4579_, v_sz_4578_);
if (v___x_4581_ == 0)
{
lean_object* v___x_4582_; 
v___x_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4582_, 0, v_bs_4580_);
return v___x_4582_;
}
else
{
lean_object* v_v_4583_; lean_object* v___x_4584_; 
v_v_4583_ = lean_array_uget_borrowed(v_bs_4580_, v_i_4579_);
lean_inc(v_v_4583_);
v___x_4584_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4583_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_bs_4580_);
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4584_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4584_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4594_; lean_object* v_bs_x27_4595_; size_t v___x_4596_; size_t v___x_4597_; lean_object* v___x_4598_; 
v_a_4593_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4593_);
lean_dec_ref(v___x_4584_);
v___x_4594_ = lean_unsigned_to_nat(0u);
v_bs_x27_4595_ = lean_array_uset(v_bs_4580_, v_i_4579_, v___x_4594_);
v___x_4596_ = ((size_t)1ULL);
v___x_4597_ = lean_usize_add(v_i_4579_, v___x_4596_);
v___x_4598_ = lean_array_uset(v_bs_x27_4595_, v_i_4579_, v_a_4593_);
v_i_4579_ = v___x_4597_;
v_bs_4580_ = v___x_4598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4600_, lean_object* v_i_4601_, lean_object* v_bs_4602_){
_start:
{
size_t v_sz_boxed_4603_; size_t v_i_boxed_4604_; lean_object* v_res_4605_; 
v_sz_boxed_4603_ = lean_unbox_usize(v_sz_4600_);
lean_dec(v_sz_4600_);
v_i_boxed_4604_ = lean_unbox_usize(v_i_4601_);
lean_dec(v_i_4601_);
v_res_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4603_, v_i_boxed_4604_, v_bs_4602_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4606_){
_start:
{
if (lean_obj_tag(v_x_4606_) == 4)
{
lean_object* v_elems_4607_; size_t v_sz_4608_; size_t v___x_4609_; lean_object* v___x_4610_; 
v_elems_4607_ = lean_ctor_get(v_x_4606_, 0);
lean_inc_ref(v_elems_4607_);
lean_dec_ref(v_x_4606_);
v_sz_4608_ = lean_array_size(v_elems_4607_);
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4608_, v___x_4609_, v_elems_4607_);
return v___x_4610_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4611_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4612_ = lean_unsigned_to_nat(80u);
v___x_4613_ = l_Lean_Json_pretty(v_x_4606_, v___x_4612_);
v___x_4614_ = lean_string_append(v___x_4611_, v___x_4613_);
lean_dec_ref(v___x_4613_);
v___x_4615_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4616_ = lean_string_append(v___x_4614_, v___x_4615_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4618_, size_t v_i_4619_, lean_object* v_bs_4620_){
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
v___x_4624_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4623_);
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
lean_dec_ref(v___x_4624_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4640_, lean_object* v_i_4641_, lean_object* v_bs_4642_){
_start:
{
size_t v_sz_boxed_4643_; size_t v_i_boxed_4644_; lean_object* v_res_4645_; 
v_sz_boxed_4643_ = lean_unbox_usize(v_sz_4640_);
lean_dec(v_sz_4640_);
v_i_boxed_4644_ = lean_unbox_usize(v_i_4641_);
lean_dec(v_i_4641_);
v_res_4645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4643_, v_i_boxed_4644_, v_bs_4642_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4646_){
_start:
{
if (lean_obj_tag(v_x_4646_) == 4)
{
lean_object* v_elems_4647_; size_t v_sz_4648_; size_t v___x_4649_; lean_object* v___x_4650_; 
v_elems_4647_ = lean_ctor_get(v_x_4646_, 0);
lean_inc_ref(v_elems_4647_);
lean_dec_ref(v_x_4646_);
v_sz_4648_ = lean_array_size(v_elems_4647_);
v___x_4649_ = ((size_t)0ULL);
v___x_4650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4648_, v___x_4649_, v_elems_4647_);
return v___x_4650_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4651_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4652_ = lean_unsigned_to_nat(80u);
v___x_4653_ = l_Lean_Json_pretty(v_x_4646_, v___x_4652_);
v___x_4654_ = lean_string_append(v___x_4651_, v___x_4653_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4656_ = lean_string_append(v___x_4654_, v___x_4655_);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4658_, lean_object* v_k_4659_){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = l_Lean_Json_getObjValD(v_j_4658_, v_k_4659_);
v___x_4661_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4660_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4662_, lean_object* v_k_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4662_, v_k_4663_);
lean_dec_ref(v_k_4663_);
return v_res_4664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = 1;
v___x_4672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4676_ = lean_string_append(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = 1;
v___x_4680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4680_, v___x_4679_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4684_ = lean_string_append(v___x_4683_, v___x_4682_);
return v___x_4684_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4686_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4687_ = lean_string_append(v___x_4686_, v___x_4685_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4688_){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4690_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4688_, v___x_4689_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4700_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4700_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4700_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
v___x_4695_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4696_ = lean_string_append(v___x_4695_, v_a_4691_);
lean_dec(v_a_4691_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4696_);
v___x_4698_ = v___x_4693_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
else
{
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v_a_4701_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4690_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4690_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
lean_ctor_set_tag(v___x_4703_, 0);
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4690_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4690_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4719_, size_t v_i_4720_, lean_object* v_bs_4721_){
_start:
{
uint8_t v___x_4722_; 
v___x_4722_ = lean_usize_dec_lt(v_i_4720_, v_sz_4719_);
if (v___x_4722_ == 0)
{
return v_bs_4721_;
}
else
{
lean_object* v_v_4723_; lean_object* v___x_4724_; lean_object* v_bs_x27_4725_; lean_object* v___x_4726_; size_t v___x_4727_; size_t v___x_4728_; lean_object* v___x_4729_; 
v_v_4723_ = lean_array_uget(v_bs_4721_, v_i_4720_);
v___x_4724_ = lean_unsigned_to_nat(0u);
v_bs_x27_4725_ = lean_array_uset(v_bs_4721_, v_i_4720_, v___x_4724_);
v___x_4726_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4723_);
v___x_4727_ = ((size_t)1ULL);
v___x_4728_ = lean_usize_add(v_i_4720_, v___x_4727_);
v___x_4729_ = lean_array_uset(v_bs_x27_4725_, v_i_4720_, v___x_4726_);
v_i_4720_ = v___x_4728_;
v_bs_4721_ = v___x_4729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4731_, lean_object* v_i_4732_, lean_object* v_bs_4733_){
_start:
{
size_t v_sz_boxed_4734_; size_t v_i_boxed_4735_; lean_object* v_res_4736_; 
v_sz_boxed_4734_ = lean_unbox_usize(v_sz_4731_);
lean_dec(v_sz_4731_);
v_i_boxed_4735_ = lean_unbox_usize(v_i_4732_);
lean_dec(v_i_4732_);
v_res_4736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4734_, v_i_boxed_4735_, v_bs_4733_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4737_){
_start:
{
size_t v_sz_4738_; size_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_sz_4738_ = lean_array_size(v_a_4737_);
v___x_4739_ = ((size_t)0ULL);
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4738_, v___x_4739_, v_a_4737_);
v___x_4741_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4742_, size_t v_i_4743_, lean_object* v_bs_4744_){
_start:
{
uint8_t v___x_4745_; 
v___x_4745_ = lean_usize_dec_lt(v_i_4743_, v_sz_4742_);
if (v___x_4745_ == 0)
{
return v_bs_4744_;
}
else
{
lean_object* v_v_4746_; lean_object* v___x_4747_; lean_object* v_bs_x27_4748_; lean_object* v___x_4749_; size_t v___x_4750_; size_t v___x_4751_; lean_object* v___x_4752_; 
v_v_4746_ = lean_array_uget(v_bs_4744_, v_i_4743_);
v___x_4747_ = lean_unsigned_to_nat(0u);
v_bs_x27_4748_ = lean_array_uset(v_bs_4744_, v_i_4743_, v___x_4747_);
v___x_4749_ = l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4746_);
v___x_4750_ = ((size_t)1ULL);
v___x_4751_ = lean_usize_add(v_i_4743_, v___x_4750_);
v___x_4752_ = lean_array_uset(v_bs_x27_4748_, v_i_4743_, v___x_4749_);
v_i_4743_ = v___x_4751_;
v_bs_4744_ = v___x_4752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4754_, lean_object* v_i_4755_, lean_object* v_bs_4756_){
_start:
{
size_t v_sz_boxed_4757_; size_t v_i_boxed_4758_; lean_object* v_res_4759_; 
v_sz_boxed_4757_ = lean_unbox_usize(v_sz_4754_);
lean_dec(v_sz_4754_);
v_i_boxed_4758_ = lean_unbox_usize(v_i_4755_);
lean_dec(v_i_4755_);
v_res_4759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4757_, v_i_boxed_4758_, v_bs_4756_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4760_){
_start:
{
size_t v_sz_4761_; size_t v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_sz_4761_ = lean_array_size(v_a_4760_);
v___x_4762_ = ((size_t)0ULL);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4761_, v___x_4762_, v_a_4760_);
v___x_4764_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4765_){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4766_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4767_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4765_);
v___x_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = lean_box(0);
v___x_4770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4768_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
lean_ctor_set(v___x_4771_, 1, v___x_4769_);
v___x_4772_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4773_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4771_, v___x_4772_);
v___x_4774_ = l_Lean_Json_mkObj(v___x_4773_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4786_ = 1;
v___x_4787_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4787_, v___x_4786_);
return v___x_4788_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4789_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4790_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4791_ = lean_string_append(v___x_4790_, v___x_4789_);
return v___x_4791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4794_ = lean_string_append(v___x_4793_, v___x_4792_);
return v___x_4794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4797_ = lean_string_append(v___x_4796_, v___x_4795_);
return v___x_4797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4798_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4799_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4800_ = lean_string_append(v___x_4799_, v___x_4798_);
return v___x_4800_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4803_ = lean_string_append(v___x_4802_, v___x_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4804_){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4804_);
v___x_4806_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4804_, v___x_4805_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_json_4804_);
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4816_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4816_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4811_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
v___x_4812_ = lean_string_append(v___x_4811_, v_a_4807_);
lean_dec(v_a_4807_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4812_);
v___x_4814_ = v___x_4809_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
else
{
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
lean_dec(v_json_4804_);
v_a_4817_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4806_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4806_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set_tag(v___x_4819_, 0);
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_a_4825_ = lean_ctor_get(v___x_4806_, 0);
lean_inc(v_a_4825_);
lean_dec_ref(v___x_4806_);
v___x_4826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4827_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4804_, v___x_4826_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4837_; 
lean_dec(v_a_4825_);
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
v___x_4832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
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
lean_dec(v_a_4825_);
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
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4854_; 
v_a_4846_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4848_ = v___x_4827_;
v_isShared_4849_ = v_isSharedCheck_4854_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4827_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4854_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4850_, 0, v_a_4825_);
lean_ctor_set(v___x_4850_, 1, v_a_4846_);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v___x_4850_);
v___x_4852_ = v___x_4848_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4857_){
_start:
{
lean_object* v_module_4858_; lean_object* v_decl_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4882_; 
v_module_4858_ = lean_ctor_get(v_x_4857_, 0);
v_decl_4859_ = lean_ctor_get(v_x_4857_, 1);
v_isSharedCheck_4882_ = !lean_is_exclusive(v_x_4857_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4861_ = v_x_4857_;
v_isShared_4862_ = v_isSharedCheck_4882_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_decl_4859_);
lean_inc(v_module_4858_);
lean_dec(v_x_4857_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4882_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4863_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4864_ = 1;
v___x_4865_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4858_, v___x_4864_);
v___x_4866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 1, v___x_4866_);
lean_ctor_set(v___x_4861_, 0, v___x_4863_);
v___x_4868_ = v___x_4861_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4863_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v___x_4866_);
v___x_4868_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4869_ = lean_box(0);
v___x_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4859_, v___x_4864_);
v___x_4873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4871_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___x_4875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
lean_ctor_set(v___x_4875_, 1, v___x_4869_);
v___x_4876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
lean_ctor_set(v___x_4876_, 1, v___x_4869_);
v___x_4877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4870_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4879_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4877_, v___x_4878_);
v___x_4880_ = l_Lean_Json_mkObj(v___x_4879_);
return v___x_4880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4885_, lean_object* v_k_4886_){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = l_Lean_Json_getObjValD(v_j_4885_, v_k_4886_);
v___x_4888_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4887_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4889_, lean_object* v_k_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4889_, v_k_4890_);
lean_dec_ref(v_k_4890_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4894_){
_start:
{
if (lean_obj_tag(v_x_4894_) == 0)
{
lean_object* v___x_4895_; 
v___x_4895_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4895_;
}
else
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4894_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4913_; 
v_a_4905_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4907_ = v___x_4896_;
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4896_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
v___x_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4909_, 0, v_a_4905_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4909_);
v___x_4911_ = v___x_4907_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4914_, lean_object* v_k_4915_){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = l_Lean_Json_getObjValD(v_j_4914_, v_k_4915_);
v___x_4917_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4918_, lean_object* v_k_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4918_, v_k_4919_);
lean_dec_ref(v_k_4919_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4923_){
_start:
{
if (lean_obj_tag(v_x_4923_) == 0)
{
lean_object* v___x_4924_; 
v___x_4924_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; 
v___x_4925_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4923_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
else
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4942_; 
v_a_4934_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4936_ = v___x_4925_;
v_isShared_4937_ = v_isSharedCheck_4942_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4925_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4942_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4938_; lean_object* v___x_4940_; 
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_a_4934_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v___x_4938_);
v___x_4940_ = v___x_4936_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4943_, lean_object* v_k_4944_){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4945_ = l_Lean_Json_getObjValD(v_j_4943_, v_k_4944_);
v___x_4946_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4947_, lean_object* v_k_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4947_, v_k_4948_);
lean_dec_ref(v_k_4948_);
return v_res_4949_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4956_ = 1;
v___x_4957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4957_, v___x_4956_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4961_ = lean_string_append(v___x_4960_, v___x_4959_);
return v___x_4961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4965_ = 1;
v___x_4966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4966_, v___x_4965_);
return v___x_4967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4970_ = lean_string_append(v___x_4969_, v___x_4968_);
return v___x_4970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4973_ = lean_string_append(v___x_4972_, v___x_4971_);
return v___x_4973_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4977_ = 1;
v___x_4978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4978_, v___x_4977_);
return v___x_4979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4980_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4982_ = lean_string_append(v___x_4981_, v___x_4980_);
return v___x_4982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4983_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4985_ = lean_string_append(v___x_4984_, v___x_4983_);
return v___x_4985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4989_ = 1;
v___x_4990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4991_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4990_, v___x_4989_);
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4994_ = lean_string_append(v___x_4993_, v___x_4992_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4997_ = lean_string_append(v___x_4996_, v___x_4995_);
return v___x_4997_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5001_ = 1;
v___x_5002_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_5003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5002_, v___x_5001_);
return v___x_5003_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5004_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_5005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5006_ = lean_string_append(v___x_5005_, v___x_5004_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5008_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_5009_ = lean_string_append(v___x_5008_, v___x_5007_);
return v___x_5009_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5014_ = 1;
v___x_5015_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_5016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5015_, v___x_5014_);
return v___x_5016_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_5018_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5019_ = lean_string_append(v___x_5018_, v___x_5017_);
return v___x_5019_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5021_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_5022_ = lean_string_append(v___x_5021_, v___x_5020_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5026_ = 1;
v___x_5027_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_5028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5027_, v___x_5026_);
return v___x_5028_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_5030_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_5031_ = lean_string_append(v___x_5030_, v___x_5029_);
return v___x_5031_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5032_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_5033_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_5034_ = lean_string_append(v___x_5033_, v___x_5032_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_5035_){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5036_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_5035_);
v___x_5037_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_5035_, v___x_5036_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_json_5035_);
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5040_ = v___x_5037_;
v_isShared_5041_ = v_isSharedCheck_5047_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5037_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5047_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5045_; 
v___x_5042_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_5043_ = lean_string_append(v___x_5042_, v_a_5038_);
lean_dec(v_a_5038_);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5043_);
v___x_5045_ = v___x_5040_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
else
{
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec(v_json_5035_);
v_a_5048_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5037_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5037_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set_tag(v___x_5050_, 0);
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v_a_5056_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_a_5056_);
lean_dec_ref(v___x_5037_);
v___x_5057_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_5035_);
v___x_5058_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_5035_, v___x_5057_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5068_; 
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
v___x_5063_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
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
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
lean_dec_ref(v___x_5058_);
v___x_5078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_5035_);
v___x_5079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5035_, v___x_5078_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5089_; 
lean_dec(v_a_5077_);
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
v___x_5084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
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
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
lean_dec_ref(v___x_5079_);
v___x_5099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_5035_);
v___x_5100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_5035_, v___x_5099_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5110_; 
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
v___x_5105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
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
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
lean_dec_ref(v___x_5100_);
v___x_5120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_5035_);
v___x_5121_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_5035_, v___x_5120_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5131_; 
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
v___x_5126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
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
lean_dec(v_a_5056_);
lean_dec(v_json_5035_);
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
lean_dec_ref(v___x_5121_);
v___x_5141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5142_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_5035_, v___x_5141_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_a_5140_);
lean_dec(v_a_5119_);
lean_dec(v_a_5098_);
lean_dec(v_a_5077_);
lean_dec(v_a_5056_);
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
v___x_5147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
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
lean_dec(v_a_5056_);
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
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5171_; 
v_a_5161_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5163_ = v___x_5142_;
v_isShared_5164_ = v_isSharedCheck_5171_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5142_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5171_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; lean_object* v___x_5169_; 
v___x_5165_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5165_, 0, v_a_5056_);
lean_ctor_set(v___x_5165_, 1, v_a_5077_);
lean_ctor_set(v___x_5165_, 2, v_a_5098_);
lean_ctor_set(v___x_5165_, 3, v_a_5119_);
v___x_5166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5166_, 0, v___x_5165_);
lean_ctor_set(v___x_5166_, 1, v_a_5140_);
v___x_5167_ = lean_unbox(v_a_5161_);
lean_dec(v_a_5161_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*2, v___x_5167_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 0, v___x_5166_);
v___x_5169_ = v___x_5163_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5166_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5174_, lean_object* v_x_5175_){
_start:
{
if (lean_obj_tag(v_x_5175_) == 0)
{
lean_object* v___x_5176_; 
lean_dec_ref(v_k_5174_);
v___x_5176_ = lean_box(0);
return v___x_5176_;
}
else
{
lean_object* v_val_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v_val_5177_ = lean_ctor_get(v_x_5175_, 0);
lean_inc(v_val_5177_);
lean_dec_ref(v_x_5175_);
v___x_5178_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5177_);
v___x_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5179_, 0, v_k_5174_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = lean_box(0);
v___x_5181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5179_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
return v___x_5181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5182_, lean_object* v_x_5183_){
_start:
{
if (lean_obj_tag(v_x_5183_) == 0)
{
lean_object* v___x_5184_; 
lean_dec_ref(v_k_5182_);
v___x_5184_ = lean_box(0);
return v___x_5184_;
}
else
{
lean_object* v_val_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v_val_5185_ = lean_ctor_get(v_x_5183_, 0);
lean_inc(v_val_5185_);
lean_dec_ref(v_x_5183_);
v___x_5186_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5185_);
v___x_5187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5187_, 0, v_k_5182_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
v___x_5188_ = lean_box(0);
v___x_5189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5187_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
return v___x_5189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5190_){
_start:
{
lean_object* v_toLocationLink_5191_; lean_object* v_ident_x3f_5192_; uint8_t v_isDefault_5193_; lean_object* v_originSelectionRange_x3f_5194_; lean_object* v_targetUri_5195_; lean_object* v_targetRange_5196_; lean_object* v_targetSelectionRange_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v_toLocationLink_5191_ = lean_ctor_get(v_x_5190_, 0);
lean_inc_ref(v_toLocationLink_5191_);
v_ident_x3f_5192_ = lean_ctor_get(v_x_5190_, 1);
lean_inc(v_ident_x3f_5192_);
v_isDefault_5193_ = lean_ctor_get_uint8(v_x_5190_, sizeof(void*)*2);
lean_dec_ref(v_x_5190_);
v_originSelectionRange_x3f_5194_ = lean_ctor_get(v_toLocationLink_5191_, 0);
lean_inc(v_originSelectionRange_x3f_5194_);
v_targetUri_5195_ = lean_ctor_get(v_toLocationLink_5191_, 1);
lean_inc_ref(v_targetUri_5195_);
v_targetRange_5196_ = lean_ctor_get(v_toLocationLink_5191_, 2);
lean_inc_ref(v_targetRange_5196_);
v_targetSelectionRange_5197_ = lean_ctor_get(v_toLocationLink_5191_, 3);
lean_inc_ref(v_targetSelectionRange_5197_);
lean_dec_ref(v_toLocationLink_5191_);
v___x_5198_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5199_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5198_, v_originSelectionRange_x3f_5194_);
v___x_5200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5201_, 0, v_targetUri_5195_);
v___x_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5200_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
v___x_5203_ = lean_box(0);
v___x_5204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5202_);
lean_ctor_set(v___x_5204_, 1, v___x_5203_);
v___x_5205_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5206_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5196_);
v___x_5207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5205_);
lean_ctor_set(v___x_5207_, 1, v___x_5206_);
v___x_5208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
lean_ctor_set(v___x_5208_, 1, v___x_5203_);
v___x_5209_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5210_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5197_);
v___x_5211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5209_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
lean_ctor_set(v___x_5212_, 1, v___x_5203_);
v___x_5213_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5214_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5213_, v_ident_x3f_5192_);
v___x_5215_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5216_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5216_, 0, v_isDefault_5193_);
v___x_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5215_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5217_);
lean_ctor_set(v___x_5218_, 1, v___x_5203_);
v___x_5219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
lean_ctor_set(v___x_5219_, 1, v___x_5203_);
v___x_5220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5214_);
lean_ctor_set(v___x_5220_, 1, v___x_5219_);
v___x_5221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5212_);
lean_ctor_set(v___x_5221_, 1, v___x_5220_);
v___x_5222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5208_);
lean_ctor_set(v___x_5222_, 1, v___x_5221_);
v___x_5223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5204_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
v___x_5224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5199_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5226_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5224_, v___x_5225_);
v___x_5227_ = l_Lean_Json_mkObj(v___x_5226_);
return v___x_5227_;
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
l_Lean_Lsp_instInhabitedRefIdent_default = _init_l_Lean_Lsp_instInhabitedRefIdent_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent_default);
l_Lean_Lsp_instInhabitedRefIdent = _init_l_Lean_Lsp_instInhabitedRefIdent();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRefIdent);
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

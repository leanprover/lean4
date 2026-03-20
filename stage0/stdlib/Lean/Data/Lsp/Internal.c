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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_List_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instEmptyCollectionDecls;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__1 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__2 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__3 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__4 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__5 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__6 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__0_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__7 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__7_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__2_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__3_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__4_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__8 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__8_value),((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__6_value)}};
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9_value;
static const lean_closure_object l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_TreeMap_instForInProdOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9_value)} };
static const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__10 = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo = (const lean_object*)&l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__10_value;
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
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionDecls(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(1);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__0(lean_object* v_x_733_){
_start:
{
lean_object* v_snd_734_; lean_object* v_fst_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_777_; 
v_snd_734_ = lean_ctor_get(v_x_733_, 1);
v_fst_735_ = lean_ctor_get(v_x_733_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_777_ == 0)
{
v___x_737_ = v_x_733_;
v_isShared_738_ = v_isSharedCheck_777_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_735_);
lean_dec(v_x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_777_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_rangeStartPosLine_739_; lean_object* v_rangeStartPosCharacter_740_; lean_object* v_rangeEndPosLine_741_; lean_object* v_rangeEndPosCharacter_742_; lean_object* v_selectionRangeStartPosLine_743_; lean_object* v_selectionRangeStartPosCharacter_744_; lean_object* v_selectionRangeEndPosLine_745_; lean_object* v_selectionRangeEndPosCharacter_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v_rangeStartPosLine_739_ = lean_ctor_get(v_snd_734_, 0);
lean_inc(v_rangeStartPosLine_739_);
v_rangeStartPosCharacter_740_ = lean_ctor_get(v_snd_734_, 1);
lean_inc(v_rangeStartPosCharacter_740_);
v_rangeEndPosLine_741_ = lean_ctor_get(v_snd_734_, 2);
lean_inc(v_rangeEndPosLine_741_);
v_rangeEndPosCharacter_742_ = lean_ctor_get(v_snd_734_, 3);
lean_inc(v_rangeEndPosCharacter_742_);
v_selectionRangeStartPosLine_743_ = lean_ctor_get(v_snd_734_, 4);
lean_inc(v_selectionRangeStartPosLine_743_);
v_selectionRangeStartPosCharacter_744_ = lean_ctor_get(v_snd_734_, 5);
lean_inc(v_selectionRangeStartPosCharacter_744_);
v_selectionRangeEndPosLine_745_ = lean_ctor_get(v_snd_734_, 6);
lean_inc(v_selectionRangeEndPosLine_745_);
v_selectionRangeEndPosCharacter_746_ = lean_ctor_get(v_snd_734_, 7);
lean_inc(v_selectionRangeEndPosCharacter_746_);
lean_dec(v_snd_734_);
v___x_747_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_739_);
v___x_748_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_740_);
v___x_750_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
v___x_751_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_741_);
v___x_752_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
v___x_753_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_742_);
v___x_754_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_743_);
v___x_756_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
v___x_757_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_744_);
v___x_758_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
v___x_759_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_745_);
v___x_760_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_746_);
v___x_762_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(8u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = lean_array_push(v___x_764_, v___x_748_);
v___x_766_ = lean_array_push(v___x_765_, v___x_750_);
v___x_767_ = lean_array_push(v___x_766_, v___x_752_);
v___x_768_ = lean_array_push(v___x_767_, v___x_754_);
v___x_769_ = lean_array_push(v___x_768_, v___x_756_);
v___x_770_ = lean_array_push(v___x_769_, v___x_758_);
v___x_771_ = lean_array_push(v___x_770_, v___x_760_);
v___x_772_ = lean_array_push(v___x_771_, v___x_762_);
v___x_773_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_773_);
v___x_775_ = v___x_737_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_fst_735_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__1(lean_object* v_x1_778_, lean_object* v_x2_779_, lean_object* v_x3_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_x1_778_);
lean_ctor_set(v___x_781_, 1, v_x2_779_);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_x3_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDecls___lam__2(lean_object* v___f_783_, lean_object* v___f_784_, lean_object* v_m_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9));
v___x_788_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_787_, v___f_783_, v___x_786_, v_m_785_);
v___x_789_ = l_List_mapTR_loop___redArg(v___f_784_, v___x_788_, v___x_786_);
v___x_790_ = l_Lean_Json_mkObj(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instFromJsonDecls___lam__0(lean_object* v_x_797_, lean_object* v_y_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_string_dec_lt(v_x_797_, v_y_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; 
v___x_800_ = lean_string_dec_eq(v_x_797_, v_y_798_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; 
v___x_801_ = 2;
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = 1;
return v___x_802_;
}
}
else
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__0___boxed(lean_object* v_x_804_, lean_object* v_y_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Lean_Lsp_instFromJsonDecls___lam__0(v_x_804_, v_y_805_);
lean_dec_ref(v_y_805_);
lean_dec_ref(v_x_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__1(lean_object* v___f_810_, lean_object* v_m_811_, lean_object* v_k_812_, lean_object* v_v_813_){
_start:
{
if (lean_obj_tag(v_v_813_) == 4)
{
lean_object* v_elems_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_933_; 
v_elems_814_ = lean_ctor_get(v_v_813_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_v_813_);
if (v_isSharedCheck_933_ == 0)
{
v___x_816_ = v_v_813_;
v_isShared_817_ = v_isSharedCheck_933_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_elems_814_);
lean_dec(v_v_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_933_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_array_get_size(v_elems_814_);
v___x_819_ = lean_unsigned_to_nat(8u);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v___x_821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_822_ = l_Nat_reprFast(v___x_818_);
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
lean_dec_ref(v___x_822_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 0);
lean_ctor_set(v___x_816_, 0, v___x_823_);
v___x_825_ = v___x_816_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_816_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_828_);
lean_inc(v___x_829_);
v___x_830_ = l_Lean_Json_getNat_x3f(v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_839_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_830_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_840_);
lean_inc(v___x_841_);
v___x_842_ = l_Lean_Json_getNat_x3f(v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_a_851_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_842_);
v___x_852_ = lean_unsigned_to_nat(2u);
v___x_853_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_852_);
lean_inc(v___x_853_);
v___x_854_ = l_Lean_Json_getNat_x3f(v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_854_);
v___x_864_ = lean_unsigned_to_nat(3u);
v___x_865_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_864_);
lean_inc(v___x_865_);
v___x_866_ = l_Lean_Json_getNat_x3f(v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_a_863_);
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_875_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_866_);
v___x_876_ = lean_unsigned_to_nat(4u);
v___x_877_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_876_);
lean_inc(v___x_877_);
v___x_878_ = l_Lean_Json_getNat_x3f(v___x_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_875_);
lean_dec(v_a_863_);
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_878_);
v___x_888_ = lean_unsigned_to_nat(5u);
v___x_889_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_888_);
lean_inc(v___x_889_);
v___x_890_ = l_Lean_Json_getNat_x3f(v___x_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_a_887_);
lean_dec(v_a_875_);
lean_dec(v_a_863_);
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
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
v___x_900_ = lean_unsigned_to_nat(6u);
v___x_901_ = lean_array_get_borrowed(v___x_827_, v_elems_814_, v___x_900_);
lean_inc(v___x_901_);
v___x_902_ = l_Lean_Json_getNat_x3f(v___x_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_899_);
lean_dec(v_a_887_);
lean_dec(v_a_875_);
lean_dec(v_a_863_);
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_elems_814_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
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
v___x_912_ = lean_unsigned_to_nat(7u);
v___x_913_ = lean_array_get(v___x_827_, v_elems_814_, v___x_912_);
lean_dec_ref(v_elems_814_);
v___x_914_ = l_Lean_Json_getNat_x3f(v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_911_);
lean_dec(v_a_899_);
lean_dec(v_a_887_);
lean_dec(v_a_875_);
lean_dec(v_a_863_);
lean_dec(v_a_851_);
lean_dec(v_a_839_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
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
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_932_; 
v_a_923_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_925_ = v___x_914_;
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_914_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_932_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_927_, 0, v_a_839_);
lean_ctor_set(v___x_927_, 1, v_a_851_);
lean_ctor_set(v___x_927_, 2, v_a_863_);
lean_ctor_set(v___x_927_, 3, v_a_875_);
lean_ctor_set(v___x_927_, 4, v_a_887_);
lean_ctor_set(v___x_927_, 5, v_a_899_);
lean_ctor_set(v___x_927_, 6, v_a_911_);
lean_ctor_set(v___x_927_, 7, v_a_923_);
v___x_928_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_810_, v_k_812_, v___x_927_, v_m_811_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
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
lean_object* v___x_934_; 
lean_dec(v_v_813_);
lean_dec_ref(v_k_812_);
lean_dec(v_m_811_);
lean_dec_ref(v___f_810_);
v___x_934_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDecls___lam__2(lean_object* v___x_935_, lean_object* v___f_936_, lean_object* v_j_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Json_getObj_x3f(v_j_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v___f_936_);
lean_dec_ref(v___x_935_);
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
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_938_);
v___x_948_ = lean_box(1);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_935_, v___f_936_, v___x_948_, v_a_947_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk(lean_object* v_range_981_, lean_object* v_parentDecl_x3f_982_){
_start:
{
if (lean_obj_tag(v_parentDecl_x3f_982_) == 0)
{
lean_object* v_start_983_; lean_object* v_end_984_; lean_object* v_line_985_; lean_object* v_character_986_; lean_object* v_line_987_; lean_object* v_character_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_start_983_ = lean_ctor_get(v_range_981_, 0);
v_end_984_ = lean_ctor_get(v_range_981_, 1);
v_line_985_ = lean_ctor_get(v_start_983_, 0);
v_character_986_ = lean_ctor_get(v_start_983_, 1);
v_line_987_ = lean_ctor_get(v_end_984_, 0);
v_character_988_ = lean_ctor_get(v_end_984_, 1);
v___x_989_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
lean_inc(v_character_988_);
lean_inc(v_line_987_);
lean_inc(v_character_986_);
lean_inc(v_line_985_);
v___x_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_990_, 0, v_line_985_);
lean_ctor_set(v___x_990_, 1, v_character_986_);
lean_ctor_set(v___x_990_, 2, v_line_987_);
lean_ctor_set(v___x_990_, 3, v_character_988_);
lean_ctor_set(v___x_990_, 4, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_start_991_; lean_object* v_end_992_; lean_object* v_line_993_; lean_object* v_character_994_; lean_object* v_line_995_; lean_object* v_character_996_; lean_object* v_val_997_; lean_object* v___x_998_; 
v_start_991_ = lean_ctor_get(v_range_981_, 0);
v_end_992_ = lean_ctor_get(v_range_981_, 1);
v_line_993_ = lean_ctor_get(v_start_991_, 0);
v_character_994_ = lean_ctor_get(v_start_991_, 1);
v_line_995_ = lean_ctor_get(v_end_992_, 0);
v_character_996_ = lean_ctor_get(v_end_992_, 1);
v_val_997_ = lean_ctor_get(v_parentDecl_x3f_982_, 0);
lean_inc(v_val_997_);
lean_inc(v_character_996_);
lean_inc(v_line_995_);
lean_inc(v_character_994_);
lean_inc(v_line_993_);
v___x_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_998_, 0, v_line_993_);
lean_ctor_set(v___x_998_, 1, v_character_994_);
lean_ctor_set(v___x_998_, 2, v_line_995_);
lean_ctor_set(v___x_998_, 3, v_character_996_);
lean_ctor_set(v___x_998_, 4, v_val_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_mk___boxed(lean_object* v_range_999_, lean_object* v_parentDecl_x3f_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Lsp_RefInfo_Location_mk(v_range_999_, v_parentDecl_x3f_1000_);
lean_dec(v_parentDecl_x3f_1000_);
lean_dec_ref(v_range_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range(lean_object* v_l_1002_){
_start:
{
lean_object* v_startPosLine_1003_; lean_object* v_startPosCharacter_1004_; lean_object* v_endPosLine_1005_; lean_object* v_endPosCharacter_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_startPosLine_1003_ = lean_ctor_get(v_l_1002_, 0);
v_startPosCharacter_1004_ = lean_ctor_get(v_l_1002_, 1);
v_endPosLine_1005_ = lean_ctor_get(v_l_1002_, 2);
v_endPosCharacter_1006_ = lean_ctor_get(v_l_1002_, 3);
lean_inc(v_startPosCharacter_1004_);
lean_inc(v_startPosLine_1003_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_startPosLine_1003_);
lean_ctor_set(v___x_1007_, 1, v_startPosCharacter_1004_);
lean_inc(v_endPosCharacter_1006_);
lean_inc(v_endPosLine_1005_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_endPosLine_1005_);
lean_ctor_set(v___x_1008_, 1, v_endPosCharacter_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_range___boxed(lean_object* v_l_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Lsp_RefInfo_Location_range(v_l_1010_);
lean_dec_ref(v_l_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(lean_object* v_l_1012_){
_start:
{
lean_object* v_parentDecl_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_parentDecl_1013_ = lean_ctor_get(v_l_1012_, 4);
v___x_1014_ = lean_string_utf8_byte_size(v_parentDecl_1013_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_nat_dec_eq(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_inc_ref(v_parentDecl_1013_);
v___x_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_parentDecl_1013_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RefInfo_Location_parentDecl_x3f___boxed(lean_object* v_l_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1019_);
lean_dec_ref(v_l_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__0(lean_object* v_n_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = l_Lean_JsonNumber_fromNat(v_n_1021_);
v___x_1023_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1(lean_object* v___f_1024_, lean_object* v_l_1025_){
_start:
{
lean_object* v_startPosLine_1026_; lean_object* v_startPosCharacter_1027_; lean_object* v_endPosLine_1028_; lean_object* v_endPosCharacter_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_range_1035_; lean_object* v___x_1036_; 
v_startPosLine_1026_ = lean_ctor_get(v_l_1025_, 0);
v_startPosCharacter_1027_ = lean_ctor_get(v_l_1025_, 1);
v_endPosLine_1028_ = lean_ctor_get(v_l_1025_, 2);
v_endPosCharacter_1029_ = lean_ctor_get(v_l_1025_, 3);
v___x_1030_ = lean_box(0);
lean_inc(v_endPosCharacter_1029_);
v___x_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_endPosCharacter_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
lean_inc(v_endPosLine_1028_);
v___x_1032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_endPosLine_1028_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_inc(v_startPosCharacter_1027_);
v___x_1033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_startPosCharacter_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_inc(v_startPosLine_1026_);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_startPosLine_1026_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v_range_1035_ = l_List_mapTR_loop___redArg(v___f_1024_, v___x_1034_, v___x_1030_);
v___x_1036_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_l_1025_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = l_List_appendTR___redArg(v_range_1035_, v___x_1030_);
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v_val_1038_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_val_1038_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 3);
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_val_1038_);
v___x_1043_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1030_);
v___x_1045_ = l_List_appendTR___redArg(v_range_1035_, v___x_1044_);
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__1___boxed(lean_object* v___f_1048_, lean_object* v_l_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Lsp_instToJsonRefInfo___lam__1(v___f_1048_, v_l_1049_);
lean_dec_ref(v_l_1049_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__2(lean_object* v_locationToList_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_apply_1(v_locationToList_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRefInfo___lam__3(lean_object* v___x_1056_, lean_object* v___f_1057_, lean_object* v_locationToList_1058_, lean_object* v_i_1059_){
_start:
{
lean_object* v_definition_x3f_1060_; lean_object* v_usages_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1093_; 
v_definition_x3f_1060_ = lean_ctor_get(v_i_1059_, 0);
v_usages_1061_ = lean_ctor_get(v_i_1059_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_i_1059_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1063_ = v_i_1059_;
v_isShared_1064_ = v_isSharedCheck_1093_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_usages_1061_);
lean_inc(v_definition_x3f_1060_);
lean_dec(v_i_1059_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1093_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___y_1067_; 
v___x_1065_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1060_) == 0)
{
lean_object* v___x_1083_; 
lean_dec_ref(v_locationToList_1058_);
v___x_1083_ = lean_box(0);
v___y_1067_ = v___x_1083_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v_val_1084_ = lean_ctor_get(v_definition_x3f_1060_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_definition_x3f_1060_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v_definition_x3f_1060_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_val_1084_);
lean_dec(v_definition_x3f_1060_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_apply_1(v_locationToList_1058_, v_val_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v___y_1067_ = v___x_1090_;
goto v___jp_1066_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_inc_ref(v___x_1056_);
v___x_1068_ = l_Option_toJson___redArg(v___x_1056_, v___y_1067_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1068_);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1070_ = v___x_1063_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1071_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1072_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9));
v_sz_1073_ = lean_array_size(v_usages_1061_);
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1072_, v___f_1057_, v_sz_1073_, v___x_1074_, v_usages_1061_);
v___x_1076_ = l_Array_toJson___redArg(v___x_1056_, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1071_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1070_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_Json_mkObj(v___x_1080_);
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0(lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1190_; 
v___x_1109_ = lean_array_get_size(v_a_1108_);
v___x_1110_ = lean_unsigned_to_nat(4u);
v___x_1190_ = lean_nat_dec_eq(v___x_1109_, v___x_1110_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(5u);
v___x_1192_ = lean_nat_dec_eq(v___x_1109_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1194_ = l_Nat_reprFast(v___x_1109_);
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
else
{
goto v___jp_1111_;
}
}
else
{
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_fget_borrowed(v_a_1108_, v___x_1112_);
lean_inc(v___x_1113_);
v___x_1114_ = l_Lean_Json_getNat_x3f(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
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
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1114_);
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_array_fget_borrowed(v_a_1108_, v___x_1124_);
lean_inc(v___x_1125_);
v___x_1126_ = l_Lean_Json_getNat_x3f(v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1123_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_a_1135_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1126_);
v___x_1136_ = lean_unsigned_to_nat(2u);
v___x_1137_ = lean_array_fget_borrowed(v_a_1108_, v___x_1136_);
lean_inc(v___x_1137_);
v___x_1138_ = l_Lean_Json_getNat_x3f(v___x_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_a_1135_);
lean_dec(v_a_1123_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1138_);
v___x_1148_ = lean_unsigned_to_nat(3u);
v___x_1149_ = lean_array_fget_borrowed(v_a_1108_, v___x_1148_);
lean_inc(v___x_1149_);
v___x_1150_ = l_Lean_Json_getNat_x3f(v___x_1149_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1147_);
lean_dec(v_a_1135_);
lean_dec(v_a_1123_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1189_; 
v_a_1159_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1161_ = v___x_1150_;
v_isShared_1162_ = v_isSharedCheck_1189_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1150_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1189_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(5u);
v___x_1164_ = lean_nat_dec_eq(v___x_1109_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1165_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1166_, 0, v_a_1123_);
lean_ctor_set(v___x_1166_, 1, v_a_1135_);
lean_ctor_set(v___x_1166_, 2, v_a_1147_);
lean_ctor_set(v___x_1166_, 3, v_a_1159_);
lean_ctor_set(v___x_1166_, 4, v___x_1165_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1166_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_1161_);
v___x_1170_ = lean_array_fget_borrowed(v_a_1108_, v___x_1110_);
lean_inc(v___x_1170_);
v___x_1171_ = l_Lean_Json_getStr_x3f(v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1159_);
lean_dec(v_a_1147_);
lean_dec(v_a_1135_);
lean_dec(v_a_1123_);
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
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v_a_1180_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1182_ = v___x_1171_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1171_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1184_, 0, v_a_1123_);
lean_ctor_set(v___x_1184_, 1, v_a_1135_);
lean_ctor_set(v___x_1184_, 2, v_a_1147_);
lean_ctor_set(v___x_1184_, 3, v_a_1159_);
lean_ctor_set(v___x_1184_, 4, v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__0___boxed(lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Lsp_instFromJsonRefInfo___lam__0(v_a_1197_);
lean_dec_ref(v_a_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRefInfo___lam__1(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_toLocation_1202_, lean_object* v_j_1203_){
_start:
{
lean_object* v_definition_x3f_1205_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_j_1203_);
v___x_1238_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1203_, v___x_1199_, v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_j_1203_);
lean_dec_ref(v_toLocation_1202_);
lean_dec_ref(v___x_1201_);
lean_dec_ref(v___x_1200_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1247_; 
v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1238_);
if (lean_obj_tag(v_a_1247_) == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
v_definition_x3f_1205_ = v___x_1248_;
goto v___jp_1204_;
}
else
{
lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1266_; 
v_val_1249_ = lean_ctor_get(v_a_1247_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_a_1247_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1251_ = v_a_1247_;
v_isShared_1252_ = v_isSharedCheck_1266_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_dec(v_a_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1266_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; 
lean_inc_ref(v_toLocation_1202_);
v___x_1253_ = lean_apply_1(v_toLocation_1202_, v_val_1249_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_del_object(v___x_1251_);
lean_dec(v_j_1203_);
lean_dec_ref(v_toLocation_1202_);
lean_dec_ref(v___x_1201_);
lean_dec_ref(v___x_1200_);
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
lean_object* v_a_1262_; lean_object* v___x_1264_; 
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1253_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_a_1262_);
v___x_1264_ = v___x_1251_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
v_definition_x3f_1205_ = v___x_1264_;
goto v___jp_1204_;
}
}
}
}
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1207_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1203_, v___x_1200_, v___x_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_definition_x3f_1205_);
lean_dec_ref(v_toLocation_1202_);
lean_dec_ref(v___x_1201_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1216_; size_t v_sz_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1207_);
v_sz_1217_ = lean_array_size(v_a_1216_);
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1201_, v_toLocation_1202_, v_sz_1217_, v___x_1218_, v_a_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_definition_x3f_1205_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_definition_x3f_1205_);
lean_ctor_set(v___x_1232_, 1, v_a_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instEmptyCollectionModuleRefs(void){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_box(1);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0(lean_object* v_f_1282_, lean_object* v_a_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1283_);
lean_ctor_set(v___x_1286_, 1, v_b_1284_);
v___x_1287_ = lean_apply_2(v_f_1282_, v___x_1286_, v_c_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1(lean_object* v_toPure_1288_, lean_object* v_____do__lift_1289_){
_start:
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v_____do__lift_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v_____do__lift_1289_);
v___x_1291_ = lean_apply_2(v_toPure_1288_, lean_box(0), v_a_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2(lean_object* v_inst_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_map_1294_, lean_object* v_init_1295_, lean_object* v_f_1296_){
_start:
{
lean_object* v_toApplicative_1297_; lean_object* v_toBind_1298_; lean_object* v_toPure_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; 
v_toApplicative_1297_ = lean_ctor_get(v_inst_1292_, 0);
v_toBind_1298_ = lean_ctor_get(v_inst_1292_, 1);
lean_inc(v_toBind_1298_);
v_toPure_1299_ = lean_ctor_get(v_toApplicative_1297_, 1);
lean_inc(v_toPure_1299_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1300_, 0, v_f_1296_);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1292_, v___f_1300_, v_init_1295_, v_map_1294_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1302_, 0, v_toPure_1299_);
v___x_1303_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v___x_1301_, v___f_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg(lean_object* v_inst_1304_){
_start:
{
lean_object* v___f_1305_; 
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1305_, 0, v_inst_1304_);
return v___f_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad(lean_object* v_m_1306_, lean_object* v_inst_1307_){
_start:
{
lean_object* v___f_1308_; 
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Lsp_instForInModuleRefsProdRefIdentRefInfoOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1308_, 0, v_inst_1307_);
return v___f_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1(lean_object* v___f_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v_startPosLine_1311_; lean_object* v_startPosCharacter_1312_; lean_object* v_endPosLine_1313_; lean_object* v_endPosCharacter_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_range_1320_; lean_object* v___x_1321_; 
v_startPosLine_1311_ = lean_ctor_get(v_x_1310_, 0);
v_startPosCharacter_1312_ = lean_ctor_get(v_x_1310_, 1);
v_endPosLine_1313_ = lean_ctor_get(v_x_1310_, 2);
v_endPosCharacter_1314_ = lean_ctor_get(v_x_1310_, 3);
v___x_1315_ = lean_box(0);
lean_inc(v_endPosCharacter_1314_);
v___x_1316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_endPosCharacter_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
lean_inc(v_endPosLine_1313_);
v___x_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_endPosLine_1313_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_inc(v_startPosCharacter_1312_);
v___x_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_startPosCharacter_1312_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_inc(v_startPosLine_1311_);
v___x_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_startPosLine_1311_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v_range_1320_ = l_List_mapTR_loop___redArg(v___f_1309_, v___x_1319_, v___x_1315_);
v___x_1321_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_x_1310_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_List_appendTR___redArg(v_range_1320_, v___x_1315_);
return v___x_1322_;
}
else
{
lean_object* v_val_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
v_val_1323_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1325_ = v___x_1321_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_val_1323_);
lean_dec(v___x_1321_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 3);
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_val_1323_);
v___x_1328_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1315_);
v___x_1330_ = l_List_appendTR___redArg(v_range_1320_, v___x_1329_);
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__1___boxed(lean_object* v___f_1333_, lean_object* v_x_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Lsp_instToJsonModuleRefs___lam__1(v___f_1333_, v_x_1334_);
lean_dec_ref(v_x_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__0(lean_object* v___f_1336_, lean_object* v___f_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v_snd_1339_; lean_object* v_fst_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1401_; 
v_snd_1339_ = lean_ctor_get(v_x_1338_, 1);
v_fst_1340_ = lean_ctor_get(v_x_1338_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1342_ = v_x_1338_;
v_isShared_1343_ = v_isSharedCheck_1401_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1339_);
lean_inc(v_fst_1340_);
lean_dec(v_x_1338_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1401_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_definition_x3f_1344_; lean_object* v_usages_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1400_; 
v_definition_x3f_1344_ = lean_ctor_get(v_snd_1339_, 0);
v_usages_1345_ = lean_ctor_get(v_snd_1339_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_snd_1339_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1347_ = v_snd_1339_;
v_isShared_1348_ = v_isSharedCheck_1400_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_usages_1345_);
lean_inc(v_definition_x3f_1344_);
lean_dec(v_snd_1339_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1400_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___y_1354_; lean_object* v___y_1374_; 
v___x_1349_ = l_Lean_Lsp_RefIdent_toJson(v_fst_1340_);
v___x_1350_ = l_Lean_Json_compress(v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___closed__4));
v___x_1352_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_1344_) == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v___f_1337_);
v___x_1376_ = lean_box(0);
v___y_1354_ = v___x_1376_;
goto v___jp_1353_;
}
else
{
lean_object* v_val_1377_; lean_object* v_startPosLine_1378_; lean_object* v_startPosCharacter_1379_; lean_object* v_endPosLine_1380_; lean_object* v_endPosCharacter_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_range_1387_; lean_object* v___x_1388_; 
v_val_1377_ = lean_ctor_get(v_definition_x3f_1344_, 0);
lean_inc(v_val_1377_);
lean_dec_ref(v_definition_x3f_1344_);
v_startPosLine_1378_ = lean_ctor_get(v_val_1377_, 0);
v_startPosCharacter_1379_ = lean_ctor_get(v_val_1377_, 1);
v_endPosLine_1380_ = lean_ctor_get(v_val_1377_, 2);
v_endPosCharacter_1381_ = lean_ctor_get(v_val_1377_, 3);
v___x_1382_ = lean_box(0);
lean_inc(v_endPosCharacter_1381_);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_endPosCharacter_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
lean_inc(v_endPosLine_1380_);
v___x_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_endPosLine_1380_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
lean_inc(v_startPosCharacter_1379_);
v___x_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_startPosCharacter_1379_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
lean_inc(v_startPosLine_1378_);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_startPosLine_1378_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v_range_1387_ = l_List_mapTR_loop___redArg(v___f_1337_, v___x_1386_, v___x_1382_);
v___x_1388_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_1377_);
lean_dec(v_val_1377_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = l_List_appendTR___redArg(v_range_1387_, v___x_1382_);
v___y_1374_ = v___x_1389_;
goto v___jp_1373_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1399_; 
v_val_1390_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1392_ = v___x_1388_;
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v___x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 3);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_val_1390_);
v___x_1395_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v___x_1382_);
v___x_1397_ = l_List_appendTR___redArg(v_range_1387_, v___x_1396_);
v___y_1374_ = v___x_1397_;
goto v___jp_1373_;
}
}
}
}
v___jp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = l_Option_toJson___redArg(v___x_1351_, v___y_1354_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___x_1355_);
lean_ctor_set(v___x_1342_, 0, v___x_1352_);
v___x_1357_ = v___x_1342_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1358_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1359_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9));
v_sz_1360_ = lean_array_size(v_usages_1345_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1359_, v___f_1336_, v_sz_1360_, v___x_1361_, v_usages_1345_);
v___x_1363_ = l_Array_toJson___redArg(v___x_1351_, v___x_1362_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1363_);
lean_ctor_set(v___x_1347_, 0, v___x_1358_);
v___x_1365_ = v___x_1347_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1357_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_Json_mkObj(v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1350_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
return v___x_1370_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1374_);
v___y_1354_ = v___x_1375_;
goto v___jp_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__2(lean_object* v_x1_1402_, lean_object* v_x2_1403_, lean_object* v_x3_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_x1_1402_);
lean_ctor_set(v___x_1405_, 1, v_x2_1403_);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v_x3_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleRefs___lam__3(lean_object* v___f_1407_, lean_object* v___f_1408_, lean_object* v_m_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = ((lean_object*)(l_Lean_Lsp_instForInIdDeclsProdStringDeclInfo___closed__9));
v___x_1412_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1411_, v___f_1407_, v___x_1410_, v_m_1409_);
v___x_1413_ = l_List_mapTR_loop___redArg(v___f_1408_, v___x_1412_, v___x_1410_);
v___x_1414_ = l_Lean_Json_mkObj(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__1(lean_object* v_toLocation_1425_, lean_object* v_m_1426_, lean_object* v_k_1427_, lean_object* v_v_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Json_parse(v_k_1427_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1429_);
v___x_1439_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1448_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1439_);
v___x_1449_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___closed__11));
v___x_1450_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__3));
v___x_1451_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_1428_);
v___x_1452_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1428_, v___x_1450_, v___x_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1582_; 
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1582_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1582_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v_definition_x3f_1467_; lean_object* v_a_1502_; 
v___x_1465_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___closed__4));
if (lean_obj_tag(v_a_1461_) == 0)
{
lean_object* v___x_1504_; 
lean_del_object(v___x_1463_);
v___x_1504_ = lean_box(0);
v_definition_x3f_1467_ = v___x_1504_;
goto v___jp_1466_;
}
else
{
lean_object* v_val_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1573_; 
v_val_1505_ = lean_ctor_get(v_a_1461_, 0);
lean_inc(v_val_1505_);
lean_dec_ref(v_a_1461_);
v___x_1506_ = lean_array_get_size(v_val_1505_);
v___x_1507_ = lean_unsigned_to_nat(4u);
v___x_1573_ = lean_nat_dec_eq(v___x_1506_, v___x_1507_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(5u);
v___x_1575_ = lean_nat_dec_eq(v___x_1506_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_val_1505_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v___x_1576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_1577_ = l_Nat_reprFast(v___x_1506_);
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
lean_dec_ref(v___x_1577_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1578_);
v___x_1580_ = v___x_1463_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_del_object(v___x_1463_);
goto v___jp_1508_;
}
}
else
{
lean_del_object(v___x_1463_);
goto v___jp_1508_;
}
v___jp_1508_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_fget_borrowed(v_val_1505_, v___x_1509_);
lean_inc(v___x_1510_);
v___x_1511_ = l_Lean_Json_getNat_x3f(v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v_val_1505_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_a_1520_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1511_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_array_fget_borrowed(v_val_1505_, v___x_1521_);
lean_inc(v___x_1522_);
v___x_1523_ = l_Lean_Json_getNat_x3f(v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_a_1520_);
lean_dec(v_val_1505_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_a_1532_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1523_);
v___x_1533_ = lean_unsigned_to_nat(2u);
v___x_1534_ = lean_array_fget_borrowed(v_val_1505_, v___x_1533_);
lean_inc(v___x_1534_);
v___x_1535_ = l_Lean_Json_getNat_x3f(v___x_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_a_1532_);
lean_dec(v_a_1520_);
lean_dec(v_val_1505_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1544_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1535_);
v___x_1545_ = lean_unsigned_to_nat(3u);
v___x_1546_ = lean_array_fget_borrowed(v_val_1505_, v___x_1545_);
lean_inc(v___x_1546_);
v___x_1547_ = l_Lean_Json_getNat_x3f(v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1544_);
lean_dec(v_a_1532_);
lean_dec(v_a_1520_);
lean_dec(v_val_1505_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_a_1556_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1547_);
v___x_1557_ = lean_unsigned_to_nat(5u);
v___x_1558_ = lean_nat_dec_eq(v___x_1506_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_val_1505_);
v___x_1559_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1520_);
lean_ctor_set(v___x_1560_, 1, v_a_1532_);
lean_ctor_set(v___x_1560_, 2, v_a_1544_);
lean_ctor_set(v___x_1560_, 3, v_a_1556_);
lean_ctor_set(v___x_1560_, 4, v___x_1559_);
v_a_1502_ = v___x_1560_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_array_fget(v_val_1505_, v___x_1507_);
lean_dec(v_val_1505_);
v___x_1562_ = l_Lean_Json_getStr_x3f(v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1556_);
lean_dec(v_a_1544_);
lean_dec(v_a_1532_);
lean_dec(v_a_1520_);
lean_dec(v_a_1448_);
lean_dec(v_v_1428_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1562_);
v___x_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1520_);
lean_ctor_set(v___x_1572_, 1, v_a_1532_);
lean_ctor_set(v___x_1572_, 2, v_a_1544_);
lean_ctor_set(v___x_1572_, 3, v_a_1556_);
lean_ctor_set(v___x_1572_, 4, v_a_1571_);
v_a_1502_ = v___x_1572_;
goto v___jp_1501_;
}
}
}
}
}
}
}
}
v___jp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_1469_ = l_Lean_Json_getObjValAs_x3f___redArg(v_v_1428_, v___x_1465_, v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_definition_x3f_1467_);
lean_dec(v_a_1448_);
lean_dec(v_m_1426_);
lean_dec_ref(v_toLocation_1425_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_object* v_a_1478_; size_t v_sz_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v_a_1478_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1469_);
v_sz_1479_ = lean_array_size(v_a_1478_);
v___x_1480_ = ((size_t)0ULL);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1449_, v_toLocation_1425_, v_sz_1479_, v___x_1480_, v_a_1478_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_definition_x3f_1467_);
lean_dec(v_a_1448_);
lean_dec(v_m_1426_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1500_; 
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1492_ = v___x_1481_;
v_isShared_1493_ = v_isSharedCheck_1500_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1481_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1500_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_definition_x3f_1467_);
lean_ctor_set(v___x_1494_, 1, v_a_1490_);
v___x_1495_ = ((lean_object*)(l_Lean_Lsp_instOrdRefIdent___closed__0));
v___x_1496_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1495_, v_a_1448_, v___x_1494_, v_m_1426_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1496_);
v___x_1498_ = v___x_1492_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
v___jp_1501_:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1502_);
v_definition_x3f_1467_ = v___x_1503_;
goto v___jp_1466_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleRefs___lam__0(lean_object* v___x_1583_, lean_object* v___f_1584_, lean_object* v_j_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Json_getObj_x3f(v_j_1585_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___f_1584_);
lean_dec_ref(v___x_1583_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1586_);
v___x_1596_ = lean_box(1);
v___x_1597_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_1583_, v___f_1584_, v___x_1596_, v_a_1595_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(lean_object* v_j_1604_, lean_object* v_k_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Lean_Json_getObjValD(v_j_1604_, v_k_1605_);
v___x_1607_ = l_Lean_Json_getNat_x3f(v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0___boxed(lean_object* v_j_1608_, lean_object* v_k_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_j_1608_, v_k_1609_);
lean_dec_ref(v_k_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(lean_object* v_j_1611_, lean_object* v_k_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_Lean_Json_getObjValD(v_j_1611_, v_k_1612_);
v___x_1614_ = l_Lean_Json_getBool_x3f(v___x_1613_);
lean_dec(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1___boxed(lean_object* v_j_1615_, lean_object* v_k_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_j_1615_, v_k_1616_);
lean_dec_ref(v_k_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(size_t v_sz_1620_, size_t v_i_1621_, lean_object* v_bs_1622_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_lt(v_i_1621_, v_sz_1620_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_bs_1622_);
return v___x_1626_;
}
else
{
lean_object* v_v_1627_; 
v_v_1627_ = lean_array_uget_borrowed(v_bs_1622_, v_i_1621_);
if (lean_obj_tag(v_v_1627_) == 4)
{
lean_object* v_elems_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_elems_1628_ = lean_ctor_get(v_v_1627_, 0);
v___x_1629_ = lean_array_get_size(v_elems_1628_);
v___x_1630_ = lean_unsigned_to_nat(4u);
v___x_1631_ = lean_nat_dec_eq(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_dec_ref(v_bs_1622_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_array_fget_borrowed(v_elems_1628_, v___x_1632_);
lean_inc(v___x_1633_);
v___x_1634_ = l_Lean_Json_getStr_x3f(v___x_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_bs_1622_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1634_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_array_fget_borrowed(v_elems_1628_, v___x_1644_);
v___x_1646_ = l_Lean_Json_getBool_x3f(v___x_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1643_);
lean_dec_ref(v_bs_1622_);
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
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_a_1655_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1655_);
lean_dec_ref(v___x_1646_);
v___x_1656_ = lean_unsigned_to_nat(2u);
v___x_1657_ = lean_array_fget_borrowed(v_elems_1628_, v___x_1656_);
v___x_1658_ = l_Lean_Json_getBool_x3f(v___x_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_a_1655_);
lean_dec(v_a_1643_);
lean_dec_ref(v_bs_1622_);
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1667_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1658_);
v___x_1668_ = lean_unsigned_to_nat(3u);
v___x_1669_ = lean_array_fget_borrowed(v_elems_1628_, v___x_1668_);
v___x_1670_ = l_Lean_Json_getBool_x3f(v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1667_);
lean_dec(v_a_1655_);
lean_dec(v_a_1643_);
lean_dec_ref(v_bs_1622_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v_bs_x27_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v_a_1679_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1670_);
v_bs_x27_1680_ = lean_array_uset(v_bs_1622_, v_i_1621_, v___x_1632_);
v___x_1681_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1681_, 0, v_a_1643_);
v___x_1682_ = lean_unbox(v_a_1655_);
lean_dec(v_a_1655_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1, v___x_1682_);
v___x_1683_ = lean_unbox(v_a_1667_);
lean_dec(v_a_1667_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1 + 1, v___x_1683_);
v___x_1684_ = lean_unbox(v_a_1679_);
lean_dec(v_a_1679_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1 + 2, v___x_1684_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1621_, v___x_1685_);
v___x_1687_ = lean_array_uset(v_bs_x27_1680_, v_i_1621_, v___x_1681_);
v_i_1621_ = v___x_1686_;
v_bs_1622_ = v___x_1687_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_bs_1622_);
goto v___jp_1623_;
}
}
v___jp_1623_:
{
lean_object* v___x_1624_; 
v___x_1624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___closed__0));
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_bs_1691_){
_start:
{
size_t v_sz_boxed_1692_; size_t v_i_boxed_1693_; lean_object* v_res_1694_; 
v_sz_boxed_1692_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_1692_, v_i_boxed_1693_, v_bs_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 4)
{
lean_object* v_elems_1698_; size_t v_sz_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v_elems_1698_ = lean_ctor_get(v_x_1697_, 0);
lean_inc_ref(v_elems_1698_);
lean_dec_ref(v_x_1697_);
v_sz_1699_ = lean_array_size(v_elems_1698_);
v___x_1700_ = ((size_t)0ULL);
v___x_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2_spec__3(v_sz_1699_, v___x_1700_, v_elems_1698_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1702_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_1703_ = lean_unsigned_to_nat(80u);
v___x_1704_ = l_Lean_Json_pretty(v_x_1697_, v___x_1703_);
v___x_1705_ = lean_string_append(v___x_1702_, v___x_1704_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_1707_ = lean_string_append(v___x_1705_, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(lean_object* v_j_1709_, lean_object* v_k_1710_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = l_Lean_Json_getObjValD(v_j_1709_, v_k_1710_);
v___x_1712_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2(v___x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2___boxed(lean_object* v_j_1713_, lean_object* v_k_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_j_1713_, v_k_1714_);
lean_dec_ref(v_k_1714_);
return v_res_1715_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = 1;
v___x_1725_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__4));
v___x_1726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_1729_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__5);
v___x_1730_ = lean_string_append(v___x_1729_, v___x_1728_);
return v___x_1730_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = 1;
v___x_1734_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__8));
v___x_1735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_1737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1738_ = lean_string_append(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1741_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__10);
v___x_1742_ = lean_string_append(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = 1;
v___x_1747_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__14));
v___x_1748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1747_, v___x_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__15);
v___x_1750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1751_ = lean_string_append(v___x_1750_, v___x_1749_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1753_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__16);
v___x_1754_ = lean_string_append(v___x_1753_, v___x_1752_);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = 1;
v___x_1759_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__19));
v___x_1760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1759_, v___x_1758_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__20);
v___x_1762_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__7);
v___x_1763_ = lean_string_append(v___x_1762_, v___x_1761_);
return v___x_1763_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_1765_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__21);
v___x_1766_ = lean_string_append(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson(lean_object* v_json_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_1767_);
v___x_1769_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_1767_, v___x_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_json_1767_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__12);
v___x_1775_ = lean_string_append(v___x_1774_, v_a_1770_);
lean_dec(v_a_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_json_1767_);
v_a_1780_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1769_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1769_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 0);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_a_1788_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1769_);
v___x_1789_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
lean_inc(v_json_1767_);
v___x_1790_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_1767_, v___x_1789_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1788_);
lean_dec(v_json_1767_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1795_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__17);
v___x_1796_ = lean_string_append(v___x_1795_, v_a_1791_);
lean_dec(v_a_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1788_);
lean_dec(v_json_1767_);
v_a_1801_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1790_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1790_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_a_1809_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1790_);
v___x_1810_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1811_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2(v_json_1767_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_a_1809_);
lean_dec(v_a_1788_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1821_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1821_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1816_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__22);
v___x_1817_ = lean_string_append(v___x_1816_, v_a_1812_);
lean_dec(v_a_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1817_);
v___x_1819_ = v___x_1814_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1809_);
lean_dec(v_a_1788_);
v_a_1822_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1811_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1811_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
v_a_1830_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___x_1811_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1811_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1834_, 0, v_a_1788_);
lean_ctor_set(v___x_1834_, 1, v_a_1830_);
v___x_1835_ = lean_unbox(v_a_1809_);
lean_dec(v_a_1809_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*2, v___x_1835_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1845_ == 0)
{
return v_bs_1844_;
}
else
{
lean_object* v_v_1846_; lean_object* v_module_1847_; uint8_t v_isPrivate_1848_; uint8_t v_isAll_1849_; uint8_t v_isMeta_1850_; lean_object* v___x_1851_; lean_object* v_bs_x27_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v_v_1846_ = lean_array_uget_borrowed(v_bs_1844_, v_i_1843_);
v_module_1847_ = lean_ctor_get(v_v_1846_, 0);
lean_inc_ref(v_module_1847_);
v_isPrivate_1848_ = lean_ctor_get_uint8(v_v_1846_, sizeof(void*)*1);
v_isAll_1849_ = lean_ctor_get_uint8(v_v_1846_, sizeof(void*)*1 + 1);
v_isMeta_1850_ = lean_ctor_get_uint8(v_v_1846_, sizeof(void*)*1 + 2);
v___x_1851_ = lean_unsigned_to_nat(0u);
v_bs_x27_1852_ = lean_array_uset(v_bs_1844_, v_i_1843_, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_module_1847_);
v___x_1854_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1854_, 0, v_isPrivate_1848_);
v___x_1855_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1855_, 0, v_isAll_1849_);
v___x_1856_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1856_, 0, v_isMeta_1850_);
v___x_1857_ = lean_unsigned_to_nat(4u);
v___x_1858_ = lean_mk_empty_array_with_capacity(v___x_1857_);
v___x_1859_ = lean_array_push(v___x_1858_, v___x_1853_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1854_);
v___x_1861_ = lean_array_push(v___x_1860_, v___x_1855_);
v___x_1862_ = lean_array_push(v___x_1861_, v___x_1856_);
v___x_1863_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_add(v_i_1843_, v___x_1864_);
v___x_1866_ = lean_array_uset(v_bs_x27_1852_, v_i_1843_, v___x_1863_);
v_i_1843_ = v___x_1865_;
v_bs_1844_ = v___x_1866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1868_, lean_object* v_i_1869_, lean_object* v_bs_1870_){
_start:
{
size_t v_sz_boxed_1871_; size_t v_i_boxed_1872_; lean_object* v_res_1873_; 
v_sz_boxed_1871_ = lean_unbox_usize(v_sz_1868_);
lean_dec(v_sz_1868_);
v_i_boxed_1872_ = lean_unbox_usize(v_i_1869_);
lean_dec(v_i_1869_);
v_res_1873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_boxed_1871_, v_i_boxed_1872_, v_bs_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(lean_object* v_a_1874_){
_start:
{
size_t v_sz_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_sz_1875_ = lean_array_size(v_a_1874_);
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0_spec__0(v_sz_1875_, v___x_1876_, v_a_1874_);
v___x_1878_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
if (lean_obj_tag(v_a_1879_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_array_to_list(v_a_1880_);
return v___x_1881_;
}
else
{
lean_object* v_head_1882_; lean_object* v_tail_1883_; lean_object* v___x_1884_; 
v_head_1882_ = lean_ctor_get(v_a_1879_, 0);
lean_inc(v_head_1882_);
v_tail_1883_ = lean_ctor_get(v_a_1879_, 1);
lean_inc(v_tail_1883_);
lean_dec_ref(v_a_1879_);
v___x_1884_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1880_, v_head_1882_);
v_a_1879_ = v_tail_1883_;
v_a_1880_ = v___x_1884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson(lean_object* v_x_1888_){
_start:
{
lean_object* v_version_1889_; uint8_t v_isSetupFailure_1890_; lean_object* v_directImports_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_version_1889_ = lean_ctor_get(v_x_1888_, 0);
lean_inc(v_version_1889_);
v_isSetupFailure_1890_ = lean_ctor_get_uint8(v_x_1888_, sizeof(void*)*2);
v_directImports_1891_ = lean_ctor_get(v_x_1888_, 1);
lean_inc_ref(v_directImports_1891_);
lean_dec_ref(v_x_1888_);
v___x_1892_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_1893_ = l_Lean_JsonNumber_fromNat(v_version_1889_);
v___x_1894_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1892_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__13));
v___x_1899_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1899_, 0, v_isSetupFailure_1890_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1896_);
v___x_1902_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__18));
v___x_1903_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__0(v_directImports_1891_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1896_);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1896_);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1901_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1897_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_1910_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_1908_, v___x_1909_);
v___x_1911_ = l_Lean_Json_mkObj(v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(lean_object* v_k_1914_, lean_object* v_v_1915_, lean_object* v_t_1916_){
_start:
{
if (lean_obj_tag(v_t_1916_) == 0)
{
lean_object* v_size_1917_; lean_object* v_k_1918_; lean_object* v_v_1919_; lean_object* v_l_1920_; lean_object* v_r_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_2202_; 
v_size_1917_ = lean_ctor_get(v_t_1916_, 0);
v_k_1918_ = lean_ctor_get(v_t_1916_, 1);
v_v_1919_ = lean_ctor_get(v_t_1916_, 2);
v_l_1920_ = lean_ctor_get(v_t_1916_, 3);
v_r_1921_ = lean_ctor_get(v_t_1916_, 4);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_t_1916_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_1923_ = v_t_1916_;
v_isShared_1924_ = v_isSharedCheck_2202_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_r_1921_);
lean_inc(v_l_1920_);
lean_inc(v_v_1919_);
lean_inc(v_k_1918_);
lean_inc(v_size_1917_);
lean_dec(v_t_1916_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_2202_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_string_dec_lt(v_k_1914_, v_k_1918_);
if (v___x_1925_ == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_string_dec_eq(v_k_1914_, v_k_1918_);
if (v___x_1926_ == 0)
{
lean_object* v_impl_1927_; lean_object* v___x_1928_; 
lean_dec(v_size_1917_);
v_impl_1927_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1914_, v_v_1915_, v_r_1921_);
v___x_1928_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1920_) == 0)
{
lean_object* v_size_1929_; lean_object* v_size_1930_; lean_object* v_k_1931_; lean_object* v_v_1932_; lean_object* v_l_1933_; lean_object* v_r_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_size_1929_ = lean_ctor_get(v_l_1920_, 0);
v_size_1930_ = lean_ctor_get(v_impl_1927_, 0);
lean_inc(v_size_1930_);
v_k_1931_ = lean_ctor_get(v_impl_1927_, 1);
lean_inc(v_k_1931_);
v_v_1932_ = lean_ctor_get(v_impl_1927_, 2);
lean_inc(v_v_1932_);
v_l_1933_ = lean_ctor_get(v_impl_1927_, 3);
lean_inc(v_l_1933_);
v_r_1934_ = lean_ctor_get(v_impl_1927_, 4);
lean_inc(v_r_1934_);
v___x_1935_ = lean_unsigned_to_nat(3u);
v___x_1936_ = lean_nat_mul(v___x_1935_, v_size_1929_);
v___x_1937_ = lean_nat_dec_lt(v___x_1936_, v_size_1930_);
lean_dec(v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec(v_r_1934_);
lean_dec(v_l_1933_);
lean_dec(v_v_1932_);
lean_dec(v_k_1931_);
v___x_1938_ = lean_nat_add(v___x_1928_, v_size_1929_);
v___x_1939_ = lean_nat_add(v___x_1938_, v_size_1930_);
lean_dec(v_size_1930_);
lean_dec(v___x_1938_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_impl_1927_);
lean_ctor_set(v___x_1923_, 0, v___x_1939_);
v___x_1941_ = v___x_1923_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_l_1920_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v_impl_1927_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
else
{
lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2006_; 
v_isSharedCheck_2006_ = !lean_is_exclusive(v_impl_1927_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2007_ = lean_ctor_get(v_impl_1927_, 4);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_impl_1927_, 3);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_impl_1927_, 2);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_impl_1927_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_impl_1927_, 0);
lean_dec(v_unused_2011_);
v___x_1944_ = v_impl_1927_;
v_isShared_1945_ = v_isSharedCheck_2006_;
goto v_resetjp_1943_;
}
else
{
lean_dec(v_impl_1927_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2006_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_size_1946_; lean_object* v_k_1947_; lean_object* v_v_1948_; lean_object* v_l_1949_; lean_object* v_r_1950_; lean_object* v_size_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_size_1946_ = lean_ctor_get(v_l_1933_, 0);
v_k_1947_ = lean_ctor_get(v_l_1933_, 1);
v_v_1948_ = lean_ctor_get(v_l_1933_, 2);
v_l_1949_ = lean_ctor_get(v_l_1933_, 3);
v_r_1950_ = lean_ctor_get(v_l_1933_, 4);
v_size_1951_ = lean_ctor_get(v_r_1934_, 0);
v___x_1952_ = lean_unsigned_to_nat(2u);
v___x_1953_ = lean_nat_mul(v___x_1952_, v_size_1951_);
v___x_1954_ = lean_nat_dec_lt(v_size_1946_, v___x_1953_);
lean_dec(v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1982_; 
lean_inc(v_r_1950_);
lean_inc(v_l_1949_);
lean_inc(v_v_1948_);
lean_inc(v_k_1947_);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_l_1933_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; lean_object* v_unused_1984_; lean_object* v_unused_1985_; lean_object* v_unused_1986_; lean_object* v_unused_1987_; 
v_unused_1983_ = lean_ctor_get(v_l_1933_, 4);
lean_dec(v_unused_1983_);
v_unused_1984_ = lean_ctor_get(v_l_1933_, 3);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_l_1933_, 2);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_l_1933_, 1);
lean_dec(v_unused_1986_);
v_unused_1987_ = lean_ctor_get(v_l_1933_, 0);
lean_dec(v_unused_1987_);
v___x_1956_ = v_l_1933_;
v_isShared_1957_ = v_isSharedCheck_1982_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_l_1933_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1982_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1972_; 
v___x_1958_ = lean_nat_add(v___x_1928_, v_size_1929_);
v___x_1959_ = lean_nat_add(v___x_1958_, v_size_1930_);
lean_dec(v_size_1930_);
if (lean_obj_tag(v_l_1949_) == 0)
{
lean_object* v_size_1980_; 
v_size_1980_ = lean_ctor_get(v_l_1949_, 0);
lean_inc(v_size_1980_);
v___y_1972_ = v_size_1980_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___y_1972_ = v___x_1981_;
goto v___jp_1971_;
}
v___jp_1960_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_nat_add(v___y_1961_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec(v___y_1961_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v_r_1934_);
lean_ctor_set(v___x_1956_, 3, v_r_1950_);
lean_ctor_set(v___x_1956_, 2, v_v_1932_);
lean_ctor_set(v___x_1956_, 1, v_k_1931_);
lean_ctor_set(v___x_1956_, 0, v___x_1964_);
v___x_1966_ = v___x_1956_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_k_1931_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_v_1932_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_r_1950_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_r_1934_);
v___x_1966_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_1966_);
lean_ctor_set(v___x_1944_, 3, v___y_1962_);
lean_ctor_set(v___x_1944_, 2, v_v_1948_);
lean_ctor_set(v___x_1944_, 1, v_k_1947_);
lean_ctor_set(v___x_1944_, 0, v___x_1959_);
v___x_1968_ = v___x_1944_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v___y_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_nat_add(v___x_1958_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec(v___x_1958_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_l_1949_);
lean_ctor_set(v___x_1923_, 0, v___x_1973_);
v___x_1975_ = v___x_1923_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_1979_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_1979_, 3, v_l_1920_);
lean_ctor_set(v_reuseFailAlloc_1979_, 4, v_l_1949_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_nat_add(v___x_1928_, v_size_1951_);
if (lean_obj_tag(v_r_1950_) == 0)
{
lean_object* v_size_1977_; 
v_size_1977_ = lean_ctor_get(v_r_1950_, 0);
lean_inc(v_size_1977_);
v___y_1961_ = v___x_1976_;
v___y_1962_ = v___x_1975_;
v___y_1963_ = v_size_1977_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___y_1961_ = v___x_1976_;
v___y_1962_ = v___x_1975_;
v___y_1963_ = v___x_1978_;
goto v___jp_1960_;
}
}
}
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_del_object(v___x_1923_);
v___x_1988_ = lean_nat_add(v___x_1928_, v_size_1929_);
v___x_1989_ = lean_nat_add(v___x_1988_, v_size_1930_);
lean_dec(v_size_1930_);
v___x_1990_ = lean_nat_add(v___x_1988_, v_size_1946_);
lean_dec(v___x_1988_);
lean_inc_ref(v_l_1920_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_1933_);
lean_ctor_set(v___x_1944_, 3, v_l_1920_);
lean_ctor_set(v___x_1944_, 2, v_v_1919_);
lean_ctor_set(v___x_1944_, 1, v_k_1918_);
lean_ctor_set(v___x_1944_, 0, v___x_1990_);
v___x_1992_ = v___x_1944_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_l_1920_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_l_1933_);
v___x_1992_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_isSharedCheck_1999_ = !lean_is_exclusive(v_l_1920_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2000_ = lean_ctor_get(v_l_1920_, 4);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_l_1920_, 3);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_l_1920_, 2);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_l_1920_, 1);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_l_1920_, 0);
lean_dec(v_unused_2004_);
v___x_1994_ = v_l_1920_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v_l_1920_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 4, v_r_1934_);
lean_ctor_set(v___x_1994_, 3, v___x_1992_);
lean_ctor_set(v___x_1994_, 2, v_v_1932_);
lean_ctor_set(v___x_1994_, 1, v_k_1931_);
lean_ctor_set(v___x_1994_, 0, v___x_1989_);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_k_1931_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_v_1932_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v_r_1934_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2012_; 
v_l_2012_ = lean_ctor_get(v_impl_1927_, 3);
lean_inc(v_l_2012_);
if (lean_obj_tag(v_l_2012_) == 0)
{
lean_object* v_r_2013_; lean_object* v_k_2014_; lean_object* v_v_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2038_; 
v_r_2013_ = lean_ctor_get(v_impl_1927_, 4);
v_k_2014_ = lean_ctor_get(v_impl_1927_, 1);
v_v_2015_ = lean_ctor_get(v_impl_1927_, 2);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_impl_1927_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2039_ = lean_ctor_get(v_impl_1927_, 3);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_impl_1927_, 0);
lean_dec(v_unused_2040_);
v___x_2017_ = v_impl_1927_;
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_r_2013_);
lean_inc(v_v_2015_);
lean_inc(v_k_2014_);
lean_dec(v_impl_1927_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_k_2019_; lean_object* v_v_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2034_; 
v_k_2019_ = lean_ctor_get(v_l_2012_, 1);
v_v_2020_ = lean_ctor_get(v_l_2012_, 2);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_l_2012_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2035_ = lean_ctor_get(v_l_2012_, 4);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_l_2012_, 3);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_l_2012_, 0);
lean_dec(v_unused_2037_);
v___x_2022_ = v_l_2012_;
v_isShared_2023_ = v_isSharedCheck_2034_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_v_2020_);
lean_inc(v_k_2019_);
lean_dec(v_l_2012_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2034_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2013_, 2);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 4, v_r_2013_);
lean_ctor_set(v___x_2022_, 3, v_r_2013_);
lean_ctor_set(v___x_2022_, 2, v_v_1919_);
lean_ctor_set(v___x_2022_, 1, v_k_1918_);
lean_ctor_set(v___x_2022_, 0, v___x_1928_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_r_2013_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_r_2013_);
v___x_2026_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
lean_inc(v_r_2013_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 3, v_r_2013_);
lean_ctor_set(v___x_2017_, 0, v___x_1928_);
v___x_2028_ = v___x_2017_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_k_2014_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_v_2015_);
lean_ctor_set(v_reuseFailAlloc_2032_, 3, v_r_2013_);
lean_ctor_set(v_reuseFailAlloc_2032_, 4, v_r_2013_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v___x_2028_);
lean_ctor_set(v___x_1923_, 3, v___x_2026_);
lean_ctor_set(v___x_1923_, 2, v_v_2020_);
lean_ctor_set(v___x_1923_, 1, v_k_2019_);
lean_ctor_set(v___x_1923_, 0, v___x_2024_);
v___x_2030_ = v___x_1923_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_k_2019_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_v_2020_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
}
else
{
lean_object* v_r_2041_; 
v_r_2041_ = lean_ctor_get(v_impl_1927_, 4);
lean_inc(v_r_2041_);
if (lean_obj_tag(v_r_2041_) == 0)
{
lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2054_; 
v_k_2042_ = lean_ctor_get(v_impl_1927_, 1);
v_v_2043_ = lean_ctor_get(v_impl_1927_, 2);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_impl_1927_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2055_ = lean_ctor_get(v_impl_1927_, 4);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_impl_1927_, 3);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_impl_1927_, 0);
lean_dec(v_unused_2057_);
v___x_2045_ = v_impl_1927_;
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_v_2043_);
lean_inc(v_k_2042_);
lean_dec(v_impl_1927_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_unsigned_to_nat(3u);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_l_2012_);
lean_ctor_set(v___x_2045_, 2, v_v_1919_);
lean_ctor_set(v___x_2045_, 1, v_k_1918_);
lean_ctor_set(v___x_2045_, 0, v___x_1928_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_l_2012_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_l_2012_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_r_2041_);
lean_ctor_set(v___x_1923_, 3, v___x_2049_);
lean_ctor_set(v___x_1923_, 2, v_v_2043_);
lean_ctor_set(v___x_1923_, 1, v_k_2042_);
lean_ctor_set(v___x_1923_, 0, v___x_2047_);
v___x_2051_ = v___x_1923_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_r_2041_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_unsigned_to_nat(2u);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_impl_1927_);
lean_ctor_set(v___x_1923_, 3, v_r_2041_);
lean_ctor_set(v___x_1923_, 0, v___x_2058_);
v___x_2060_ = v___x_1923_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_impl_1927_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v___x_2063_; 
lean_dec(v_v_1919_);
lean_dec(v_k_1918_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 2, v_v_1915_);
lean_ctor_set(v___x_1923_, 1, v_k_1914_);
v___x_2063_ = v___x_1923_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_size_1917_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_1914_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_1915_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_l_1920_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_r_1921_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_impl_2065_; lean_object* v___x_2066_; 
lean_dec(v_size_1917_);
v_impl_2065_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_1914_, v_v_1915_, v_l_1920_);
v___x_2066_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1921_) == 0)
{
lean_object* v_size_2067_; lean_object* v_size_2068_; lean_object* v_k_2069_; lean_object* v_v_2070_; lean_object* v_l_2071_; lean_object* v_r_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_size_2067_ = lean_ctor_get(v_r_1921_, 0);
v_size_2068_ = lean_ctor_get(v_impl_2065_, 0);
lean_inc(v_size_2068_);
v_k_2069_ = lean_ctor_get(v_impl_2065_, 1);
lean_inc(v_k_2069_);
v_v_2070_ = lean_ctor_get(v_impl_2065_, 2);
lean_inc(v_v_2070_);
v_l_2071_ = lean_ctor_get(v_impl_2065_, 3);
lean_inc(v_l_2071_);
v_r_2072_ = lean_ctor_get(v_impl_2065_, 4);
lean_inc(v_r_2072_);
v___x_2073_ = lean_unsigned_to_nat(3u);
v___x_2074_ = lean_nat_mul(v___x_2073_, v_size_2067_);
v___x_2075_ = lean_nat_dec_lt(v___x_2074_, v_size_2068_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
lean_dec(v_r_2072_);
lean_dec(v_l_2071_);
lean_dec(v_v_2070_);
lean_dec(v_k_2069_);
v___x_2076_ = lean_nat_add(v___x_2066_, v_size_2068_);
lean_dec(v_size_2068_);
v___x_2077_ = lean_nat_add(v___x_2076_, v_size_2067_);
lean_dec(v___x_2076_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 3, v_impl_2065_);
lean_ctor_set(v___x_1923_, 0, v___x_2077_);
v___x_2079_ = v___x_1923_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2080_, 3, v_impl_2065_);
lean_ctor_set(v_reuseFailAlloc_2080_, 4, v_r_1921_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
else
{
lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v_impl_2065_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2147_ = lean_ctor_get(v_impl_2065_, 4);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_impl_2065_, 3);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_impl_2065_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_impl_2065_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_impl_2065_, 0);
lean_dec(v_unused_2151_);
v___x_2082_ = v_impl_2065_;
v_isShared_2083_ = v_isSharedCheck_2146_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v_impl_2065_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2146_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_size_2084_; lean_object* v_size_2085_; lean_object* v_k_2086_; lean_object* v_v_2087_; lean_object* v_l_2088_; lean_object* v_r_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_size_2084_ = lean_ctor_get(v_l_2071_, 0);
v_size_2085_ = lean_ctor_get(v_r_2072_, 0);
v_k_2086_ = lean_ctor_get(v_r_2072_, 1);
v_v_2087_ = lean_ctor_get(v_r_2072_, 2);
v_l_2088_ = lean_ctor_get(v_r_2072_, 3);
v_r_2089_ = lean_ctor_get(v_r_2072_, 4);
v___x_2090_ = lean_unsigned_to_nat(2u);
v___x_2091_ = lean_nat_mul(v___x_2090_, v_size_2084_);
v___x_2092_ = lean_nat_dec_lt(v_size_2085_, v___x_2091_);
lean_dec(v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2121_; 
lean_inc(v_r_2089_);
lean_inc(v_l_2088_);
lean_inc(v_v_2087_);
lean_inc(v_k_2086_);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_r_2072_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2122_ = lean_ctor_get(v_r_2072_, 4);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_r_2072_, 3);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_r_2072_, 2);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_r_2072_, 1);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_r_2072_, 0);
lean_dec(v_unused_2126_);
v___x_2094_ = v_r_2072_;
v_isShared_2095_ = v_isSharedCheck_2121_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v_r_2072_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2121_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2109_; lean_object* v___y_2111_; 
v___x_2096_ = lean_nat_add(v___x_2066_, v_size_2068_);
lean_dec(v_size_2068_);
v___x_2097_ = lean_nat_add(v___x_2096_, v_size_2067_);
lean_dec(v___x_2096_);
v___x_2109_ = lean_nat_add(v___x_2066_, v_size_2084_);
if (lean_obj_tag(v_l_2088_) == 0)
{
lean_object* v_size_2119_; 
v_size_2119_ = lean_ctor_get(v_l_2088_, 0);
lean_inc(v_size_2119_);
v___y_2111_ = v_size_2119_;
goto v___jp_2110_;
}
else
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___y_2111_ = v___x_2120_;
goto v___jp_2110_;
}
v___jp_2098_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = lean_nat_add(v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 4, v_r_1921_);
lean_ctor_set(v___x_2094_, 3, v_r_2089_);
lean_ctor_set(v___x_2094_, 2, v_v_1919_);
lean_ctor_set(v___x_2094_, 1, v_k_1918_);
lean_ctor_set(v___x_2094_, 0, v___x_2102_);
v___x_2104_ = v___x_2094_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_r_2089_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_r_1921_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v___x_2104_);
lean_ctor_set(v___x_2082_, 3, v___y_2099_);
lean_ctor_set(v___x_2082_, 2, v_v_2087_);
lean_ctor_set(v___x_2082_, 1, v_k_2086_);
lean_ctor_set(v___x_2082_, 0, v___x_2097_);
v___x_2106_ = v___x_2082_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_k_2086_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_v_2087_);
lean_ctor_set(v_reuseFailAlloc_2107_, 3, v___y_2099_);
lean_ctor_set(v_reuseFailAlloc_2107_, 4, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
v___jp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_nat_add(v___x_2109_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec(v___x_2109_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_l_2088_);
lean_ctor_set(v___x_1923_, 3, v_l_2071_);
lean_ctor_set(v___x_1923_, 2, v_v_2070_);
lean_ctor_set(v___x_1923_, 1, v_k_2069_);
lean_ctor_set(v___x_1923_, 0, v___x_2112_);
v___x_2114_ = v___x_1923_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2118_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2118_, 3, v_l_2071_);
lean_ctor_set(v_reuseFailAlloc_2118_, 4, v_l_2088_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_nat_add(v___x_2066_, v_size_2067_);
if (lean_obj_tag(v_r_2089_) == 0)
{
lean_object* v_size_2116_; 
v_size_2116_ = lean_ctor_get(v_r_2089_, 0);
lean_inc(v_size_2116_);
v___y_2099_ = v___x_2114_;
v___y_2100_ = v___x_2115_;
v___y_2101_ = v_size_2116_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___y_2099_ = v___x_2114_;
v___y_2100_ = v___x_2115_;
v___y_2101_ = v___x_2117_;
goto v___jp_2098_;
}
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
lean_del_object(v___x_1923_);
v___x_2127_ = lean_nat_add(v___x_2066_, v_size_2068_);
lean_dec(v_size_2068_);
v___x_2128_ = lean_nat_add(v___x_2127_, v_size_2067_);
lean_dec(v___x_2127_);
v___x_2129_ = lean_nat_add(v___x_2066_, v_size_2067_);
v___x_2130_ = lean_nat_add(v___x_2129_, v_size_2085_);
lean_dec(v___x_2129_);
lean_inc_ref(v_r_1921_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v_r_1921_);
lean_ctor_set(v___x_2082_, 3, v_r_2072_);
lean_ctor_set(v___x_2082_, 2, v_v_1919_);
lean_ctor_set(v___x_2082_, 1, v_k_1918_);
lean_ctor_set(v___x_2082_, 0, v___x_2130_);
v___x_2132_ = v___x_2082_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_r_2072_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_r_1921_);
v___x_2132_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
v_isSharedCheck_2139_ = !lean_is_exclusive(v_r_1921_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; 
v_unused_2140_ = lean_ctor_get(v_r_1921_, 4);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_r_1921_, 3);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_r_1921_, 2);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_r_1921_, 1);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_r_1921_, 0);
lean_dec(v_unused_2144_);
v___x_2134_ = v_r_1921_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_dec(v_r_1921_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 4, v___x_2132_);
lean_ctor_set(v___x_2134_, 3, v_l_2071_);
lean_ctor_set(v___x_2134_, 2, v_v_2070_);
lean_ctor_set(v___x_2134_, 1, v_k_2069_);
lean_ctor_set(v___x_2134_, 0, v___x_2128_);
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_k_2069_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_v_2070_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_l_2071_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v___x_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2152_; 
v_l_2152_ = lean_ctor_get(v_impl_2065_, 3);
lean_inc(v_l_2152_);
if (lean_obj_tag(v_l_2152_) == 0)
{
lean_object* v_r_2153_; lean_object* v_k_2154_; lean_object* v_v_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2166_; 
v_r_2153_ = lean_ctor_get(v_impl_2065_, 4);
v_k_2154_ = lean_ctor_get(v_impl_2065_, 1);
v_v_2155_ = lean_ctor_get(v_impl_2065_, 2);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_impl_2065_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; 
v_unused_2167_ = lean_ctor_get(v_impl_2065_, 3);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_impl_2065_, 0);
lean_dec(v_unused_2168_);
v___x_2157_ = v_impl_2065_;
v_isShared_2158_ = v_isSharedCheck_2166_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_r_2153_);
lean_inc(v_v_2155_);
lean_inc(v_k_2154_);
lean_dec(v_impl_2065_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2166_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2153_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 3, v_r_2153_);
lean_ctor_set(v___x_2157_, 2, v_v_1919_);
lean_ctor_set(v___x_2157_, 1, v_k_1918_);
lean_ctor_set(v___x_2157_, 0, v___x_2066_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_r_2153_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_r_2153_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v___x_2161_);
lean_ctor_set(v___x_1923_, 3, v_l_2152_);
lean_ctor_set(v___x_1923_, 2, v_v_2155_);
lean_ctor_set(v___x_1923_, 1, v_k_2154_);
lean_ctor_set(v___x_1923_, 0, v___x_2159_);
v___x_2163_ = v___x_1923_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_l_2152_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_r_2169_; 
v_r_2169_ = lean_ctor_get(v_impl_2065_, 4);
lean_inc(v_r_2169_);
if (lean_obj_tag(v_r_2169_) == 0)
{
lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2194_; 
v_k_2170_ = lean_ctor_get(v_impl_2065_, 1);
v_v_2171_ = lean_ctor_get(v_impl_2065_, 2);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_impl_2065_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; 
v_unused_2195_ = lean_ctor_get(v_impl_2065_, 4);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_impl_2065_, 3);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_impl_2065_, 0);
lean_dec(v_unused_2197_);
v___x_2173_ = v_impl_2065_;
v_isShared_2174_ = v_isSharedCheck_2194_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
lean_dec(v_impl_2065_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2194_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2190_; 
v_k_2175_ = lean_ctor_get(v_r_2169_, 1);
v_v_2176_ = lean_ctor_get(v_r_2169_, 2);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_r_2169_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2191_ = lean_ctor_get(v_r_2169_, 4);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_r_2169_, 3);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2169_, 0);
lean_dec(v_unused_2193_);
v___x_2178_ = v_r_2169_;
v_isShared_2179_ = v_isSharedCheck_2190_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_dec(v_r_2169_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2190_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3u);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_l_2152_);
lean_ctor_set(v___x_2178_, 3, v_l_2152_);
lean_ctor_set(v___x_2178_, 2, v_v_2171_);
lean_ctor_set(v___x_2178_, 1, v_k_2170_);
lean_ctor_set(v___x_2178_, 0, v___x_2066_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_l_2152_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_l_2152_);
v___x_2182_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 4, v_l_2152_);
lean_ctor_set(v___x_2173_, 2, v_v_1919_);
lean_ctor_set(v___x_2173_, 1, v_k_1918_);
lean_ctor_set(v___x_2173_, 0, v___x_2066_);
v___x_2184_ = v___x_2173_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_l_2152_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_l_2152_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v___x_2184_);
lean_ctor_set(v___x_1923_, 3, v___x_2182_);
lean_ctor_set(v___x_1923_, 2, v_v_2176_);
lean_ctor_set(v___x_1923_, 1, v_k_2175_);
lean_ctor_set(v___x_1923_, 0, v___x_2180_);
v___x_2186_ = v___x_1923_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(2u);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v_r_2169_);
lean_ctor_set(v___x_1923_, 3, v_impl_2065_);
lean_ctor_set(v___x_1923_, 0, v___x_2198_);
v___x_2200_ = v___x_1923_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_1918_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_1919_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_impl_2065_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_r_2169_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v_k_1914_);
lean_ctor_set(v___x_2204_, 2, v_v_1915_);
lean_ctor_set(v___x_2204_, 3, v_t_1916_);
lean_ctor_set(v___x_2204_, 4, v_t_1916_);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(lean_object* v_init_2205_, lean_object* v_x_2206_){
_start:
{
if (lean_obj_tag(v_x_2206_) == 0)
{
lean_object* v_k_2207_; lean_object* v_v_2208_; lean_object* v_l_2209_; lean_object* v_r_2210_; lean_object* v___x_2211_; 
v_k_2207_ = lean_ctor_get(v_x_2206_, 1);
lean_inc(v_k_2207_);
v_v_2208_ = lean_ctor_get(v_x_2206_, 2);
lean_inc(v_v_2208_);
v_l_2209_ = lean_ctor_get(v_x_2206_, 3);
lean_inc(v_l_2209_);
v_r_2210_ = lean_ctor_get(v_x_2206_, 4);
lean_inc(v_r_2210_);
lean_dec_ref(v_x_2206_);
v___x_2211_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v_init_2205_, v_l_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec(v_r_2210_);
lean_dec(v_v_2208_);
lean_dec(v_k_2207_);
return v___x_2211_;
}
else
{
if (lean_obj_tag(v_v_2208_) == 4)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2326_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2326_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2326_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_elems_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_elems_2216_ = lean_ctor_get(v_v_2208_, 0);
lean_inc_ref(v_elems_2216_);
lean_dec_ref(v_v_2208_);
v___x_2217_ = lean_array_get_size(v_elems_2216_);
v___x_2218_ = lean_unsigned_to_nat(8u);
v___x_2219_ = lean_nat_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v___x_2220_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeclInfo___lam__0___closed__0));
v___x_2221_ = l_Nat_reprFast(v___x_2217_);
v___x_2222_ = lean_string_append(v___x_2220_, v___x_2221_);
lean_dec_ref(v___x_2221_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2222_);
v___x_2224_ = v___x_2214_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_del_object(v___x_2214_);
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2227_);
lean_inc(v___x_2228_);
v___x_2229_ = l_Lean_Json_getNat_x3f(v___x_2228_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_a_2238_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2229_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2239_);
lean_inc(v___x_2240_);
v___x_2241_ = l_Lean_Json_getNat_x3f(v___x_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_a_2250_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2241_);
v___x_2251_ = lean_unsigned_to_nat(2u);
v___x_2252_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2251_);
lean_inc(v___x_2252_);
v___x_2253_ = l_Lean_Json_getNat_x3f(v___x_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2262_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2253_);
v___x_2263_ = lean_unsigned_to_nat(3u);
v___x_2264_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2263_);
lean_inc(v___x_2264_);
v___x_2265_ = l_Lean_Json_getNat_x3f(v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2262_);
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2274_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2265_);
v___x_2275_ = lean_unsigned_to_nat(4u);
v___x_2276_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2275_);
lean_inc(v___x_2276_);
v___x_2277_ = l_Lean_Json_getNat_x3f(v___x_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_a_2274_);
lean_dec(v_a_2262_);
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_a_2286_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2277_);
v___x_2287_ = lean_unsigned_to_nat(5u);
v___x_2288_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2287_);
lean_inc(v___x_2288_);
v___x_2289_ = l_Lean_Json_getNat_x3f(v___x_2288_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2274_);
lean_dec(v_a_2262_);
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_a_2298_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2289_);
v___x_2299_ = lean_unsigned_to_nat(6u);
v___x_2300_ = lean_array_get_borrowed(v___x_2226_, v_elems_2216_, v___x_2299_);
lean_inc(v___x_2300_);
v___x_2301_ = l_Lean_Json_getNat_x3f(v___x_2300_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_a_2298_);
lean_dec(v_a_2286_);
lean_dec(v_a_2274_);
lean_dec(v_a_2262_);
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec_ref(v_elems_2216_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2301_);
v___x_2311_ = lean_unsigned_to_nat(7u);
v___x_2312_ = lean_array_get(v___x_2226_, v_elems_2216_, v___x_2311_);
lean_dec_ref(v_elems_2216_);
v___x_2313_ = l_Lean_Json_getNat_x3f(v___x_2312_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_a_2310_);
lean_dec(v_a_2298_);
lean_dec(v_a_2286_);
lean_dec(v_a_2274_);
lean_dec(v_a_2262_);
lean_dec(v_a_2250_);
lean_dec(v_a_2238_);
lean_dec(v_a_2212_);
lean_dec(v_r_2210_);
lean_dec(v_k_2207_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2313_);
v___x_2323_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2238_);
lean_ctor_set(v___x_2323_, 1, v_a_2250_);
lean_ctor_set(v___x_2323_, 2, v_a_2262_);
lean_ctor_set(v___x_2323_, 3, v_a_2274_);
lean_ctor_set(v___x_2323_, 4, v_a_2286_);
lean_ctor_set(v___x_2323_, 5, v_a_2298_);
lean_ctor_set(v___x_2323_, 6, v_a_2310_);
lean_ctor_set(v___x_2323_, 7, v_a_2322_);
v___x_2324_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_2207_, v___x_2323_, v_a_2212_);
v_init_2205_ = v___x_2324_;
v_x_2206_ = v_r_2210_;
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
lean_object* v___x_2327_; 
lean_dec_ref(v___x_2211_);
lean_dec(v_r_2210_);
lean_dec(v_v_2208_);
lean_dec(v_k_2207_);
v___x_2327_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDecls___lam__1___closed__0));
return v___x_2327_;
}
}
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_init_2205_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(lean_object* v_j_2329_, lean_object* v_k_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = l_Lean_Json_getObjValD(v_j_2329_, v_k_2330_);
v___x_2332_ = l_Lean_Json_getObj_x3f(v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2332_);
v___x_2342_ = lean_box(1);
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__7(v___x_2342_, v_a_2341_);
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1___boxed(lean_object* v_j_2344_, lean_object* v_k_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_j_2344_, v_k_2345_);
lean_dec_ref(v_k_2345_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(size_t v_sz_2347_, size_t v_i_2348_, lean_object* v_bs_2349_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_usize_dec_lt(v_i_2348_, v_sz_2347_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_bs_2349_);
return v___x_2351_;
}
else
{
lean_object* v_v_2352_; lean_object* v___x_2353_; lean_object* v_bs_x27_2354_; size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v_v_2352_ = lean_array_uget(v_bs_2349_, v_i_2348_);
v___x_2353_ = lean_unsigned_to_nat(0u);
v_bs_x27_2354_ = lean_array_uset(v_bs_2349_, v_i_2348_, v___x_2353_);
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2348_, v___x_2355_);
v___x_2357_ = lean_array_uset(v_bs_x27_2354_, v_i_2348_, v_v_2352_);
v_i_2348_ = v___x_2356_;
v_bs_2349_ = v___x_2357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10___boxed(lean_object* v_sz_2359_, lean_object* v_i_2360_, lean_object* v_bs_2361_){
_start:
{
size_t v_sz_boxed_2362_; size_t v_i_boxed_2363_; lean_object* v_res_2364_; 
v_sz_boxed_2362_ = lean_unbox_usize(v_sz_2359_);
lean_dec(v_sz_2359_);
v_i_boxed_2363_ = lean_unbox_usize(v_i_2360_);
lean_dec(v_i_2360_);
v_res_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_boxed_2362_, v_i_boxed_2363_, v_bs_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 4)
{
lean_object* v_elems_2366_; size_t v_sz_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v_elems_2366_ = lean_ctor_get(v_x_2365_, 0);
lean_inc_ref(v_elems_2366_);
lean_dec_ref(v_x_2365_);
v_sz_2367_ = lean_array_size(v_elems_2366_);
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3_spec__10(v_sz_2367_, v___x_2368_, v_elems_2366_);
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2370_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2371_ = lean_unsigned_to_nat(80u);
v___x_2372_ = l_Lean_Json_pretty(v_x_2365_, v___x_2371_);
v___x_2373_ = lean_string_append(v___x_2370_, v___x_2372_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2375_ = lean_string_append(v___x_2373_, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5___closed__0));
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_x_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_a_2390_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v___x_2381_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2381_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_a_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(lean_object* v_j_2399_, lean_object* v_k_2400_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = l_Lean_Json_getObjValD(v_j_2399_, v_k_2400_);
v___x_2402_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3_spec__5(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3___boxed(lean_object* v_j_2403_, lean_object* v_k_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_j_2403_, v_k_2404_);
lean_dec_ref(v_k_2404_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(lean_object* v_k_2406_, lean_object* v_v_2407_, lean_object* v_t_2408_){
_start:
{
if (lean_obj_tag(v_t_2408_) == 0)
{
lean_object* v_size_2409_; lean_object* v_k_2410_; lean_object* v_v_2411_; lean_object* v_l_2412_; lean_object* v_r_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2693_; 
v_size_2409_ = lean_ctor_get(v_t_2408_, 0);
v_k_2410_ = lean_ctor_get(v_t_2408_, 1);
v_v_2411_ = lean_ctor_get(v_t_2408_, 2);
v_l_2412_ = lean_ctor_get(v_t_2408_, 3);
v_r_2413_ = lean_ctor_get(v_t_2408_, 4);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_t_2408_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2415_ = v_t_2408_;
v_isShared_2416_ = v_isSharedCheck_2693_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_r_2413_);
lean_inc(v_l_2412_);
lean_inc(v_v_2411_);
lean_inc(v_k_2410_);
lean_inc(v_size_2409_);
lean_dec(v_t_2408_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2693_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_Lsp_instOrdRefIdent_ord(v_k_2406_, v_k_2410_);
switch(v___x_2417_)
{
case 0:
{
lean_object* v_impl_2418_; lean_object* v___x_2419_; 
lean_dec(v_size_2409_);
v_impl_2418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2406_, v_v_2407_, v_l_2412_);
v___x_2419_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2413_) == 0)
{
lean_object* v_size_2420_; lean_object* v_size_2421_; lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_l_2424_; lean_object* v_r_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_size_2420_ = lean_ctor_get(v_r_2413_, 0);
v_size_2421_ = lean_ctor_get(v_impl_2418_, 0);
lean_inc(v_size_2421_);
v_k_2422_ = lean_ctor_get(v_impl_2418_, 1);
lean_inc(v_k_2422_);
v_v_2423_ = lean_ctor_get(v_impl_2418_, 2);
lean_inc(v_v_2423_);
v_l_2424_ = lean_ctor_get(v_impl_2418_, 3);
lean_inc(v_l_2424_);
v_r_2425_ = lean_ctor_get(v_impl_2418_, 4);
lean_inc(v_r_2425_);
v___x_2426_ = lean_unsigned_to_nat(3u);
v___x_2427_ = lean_nat_mul(v___x_2426_, v_size_2420_);
v___x_2428_ = lean_nat_dec_lt(v___x_2427_, v_size_2421_);
lean_dec(v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_dec(v_r_2425_);
lean_dec(v_l_2424_);
lean_dec(v_v_2423_);
lean_dec(v_k_2422_);
v___x_2429_ = lean_nat_add(v___x_2419_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2430_ = lean_nat_add(v___x_2429_, v_size_2420_);
lean_dec(v___x_2429_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 3, v_impl_2418_);
lean_ctor_set(v___x_2415_, 0, v___x_2430_);
v___x_2432_ = v___x_2415_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2433_, 4, v_r_2413_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2499_; 
v_isSharedCheck_2499_ = !lean_is_exclusive(v_impl_2418_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; lean_object* v_unused_2504_; 
v_unused_2500_ = lean_ctor_get(v_impl_2418_, 4);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_impl_2418_, 3);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_impl_2418_, 2);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_impl_2418_, 1);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_impl_2418_, 0);
lean_dec(v_unused_2504_);
v___x_2435_ = v_impl_2418_;
v_isShared_2436_ = v_isSharedCheck_2499_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_impl_2418_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2499_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_size_2437_; lean_object* v_size_2438_; lean_object* v_k_2439_; lean_object* v_v_2440_; lean_object* v_l_2441_; lean_object* v_r_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_size_2437_ = lean_ctor_get(v_l_2424_, 0);
v_size_2438_ = lean_ctor_get(v_r_2425_, 0);
v_k_2439_ = lean_ctor_get(v_r_2425_, 1);
v_v_2440_ = lean_ctor_get(v_r_2425_, 2);
v_l_2441_ = lean_ctor_get(v_r_2425_, 3);
v_r_2442_ = lean_ctor_get(v_r_2425_, 4);
v___x_2443_ = lean_unsigned_to_nat(2u);
v___x_2444_ = lean_nat_mul(v___x_2443_, v_size_2437_);
v___x_2445_ = lean_nat_dec_lt(v_size_2438_, v___x_2444_);
lean_dec(v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2474_; 
lean_inc(v_r_2442_);
lean_inc(v_l_2441_);
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_r_2425_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; lean_object* v_unused_2479_; 
v_unused_2475_ = lean_ctor_get(v_r_2425_, 4);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_r_2425_, 3);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_r_2425_, 2);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_r_2425_, 1);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_r_2425_, 0);
lean_dec(v_unused_2479_);
v___x_2447_ = v_r_2425_;
v_isShared_2448_ = v_isSharedCheck_2474_;
goto v_resetjp_2446_;
}
else
{
lean_dec(v_r_2425_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2474_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___x_2462_; lean_object* v___y_2464_; 
v___x_2449_ = lean_nat_add(v___x_2419_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2450_ = lean_nat_add(v___x_2449_, v_size_2420_);
lean_dec(v___x_2449_);
v___x_2462_ = lean_nat_add(v___x_2419_, v_size_2437_);
if (lean_obj_tag(v_l_2441_) == 0)
{
lean_object* v_size_2472_; 
v_size_2472_ = lean_ctor_get(v_l_2441_, 0);
lean_inc(v_size_2472_);
v___y_2464_ = v_size_2472_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_unsigned_to_nat(0u);
v___y_2464_ = v___x_2473_;
goto v___jp_2463_;
}
v___jp_2451_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_nat_add(v___y_2452_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec(v___y_2452_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 4, v_r_2413_);
lean_ctor_set(v___x_2447_, 3, v_r_2442_);
lean_ctor_set(v___x_2447_, 2, v_v_2411_);
lean_ctor_set(v___x_2447_, 1, v_k_2410_);
lean_ctor_set(v___x_2447_, 0, v___x_2455_);
v___x_2457_ = v___x_2447_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_r_2442_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_r_2413_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___x_2457_);
lean_ctor_set(v___x_2435_, 3, v___y_2453_);
lean_ctor_set(v___x_2435_, 2, v_v_2440_);
lean_ctor_set(v___x_2435_, 1, v_k_2439_);
lean_ctor_set(v___x_2435_, 0, v___x_2450_);
v___x_2459_ = v___x_2435_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v___y_2453_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
v___jp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = lean_nat_add(v___x_2462_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec(v___x_2462_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_l_2441_);
lean_ctor_set(v___x_2415_, 3, v_l_2424_);
lean_ctor_set(v___x_2415_, 2, v_v_2423_);
lean_ctor_set(v___x_2415_, 1, v_k_2422_);
lean_ctor_set(v___x_2415_, 0, v___x_2465_);
v___x_2467_ = v___x_2415_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_l_2441_);
v___x_2467_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_nat_add(v___x_2419_, v_size_2420_);
if (lean_obj_tag(v_r_2442_) == 0)
{
lean_object* v_size_2469_; 
v_size_2469_ = lean_ctor_get(v_r_2442_, 0);
lean_inc(v_size_2469_);
v___y_2452_ = v___x_2468_;
v___y_2453_ = v___x_2467_;
v___y_2454_ = v_size_2469_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_unsigned_to_nat(0u);
v___y_2452_ = v___x_2468_;
v___y_2453_ = v___x_2467_;
v___y_2454_ = v___x_2470_;
goto v___jp_2451_;
}
}
}
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_del_object(v___x_2415_);
v___x_2480_ = lean_nat_add(v___x_2419_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2481_ = lean_nat_add(v___x_2480_, v_size_2420_);
lean_dec(v___x_2480_);
v___x_2482_ = lean_nat_add(v___x_2419_, v_size_2420_);
v___x_2483_ = lean_nat_add(v___x_2482_, v_size_2438_);
lean_dec(v___x_2482_);
lean_inc_ref(v_r_2413_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_r_2413_);
lean_ctor_set(v___x_2435_, 3, v_r_2425_);
lean_ctor_set(v___x_2435_, 2, v_v_2411_);
lean_ctor_set(v___x_2435_, 1, v_k_2410_);
lean_ctor_set(v___x_2435_, 0, v___x_2483_);
v___x_2485_ = v___x_2435_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_r_2425_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v_r_2413_);
v___x_2485_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
v_isSharedCheck_2492_ = !lean_is_exclusive(v_r_2413_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; lean_object* v_unused_2497_; 
v_unused_2493_ = lean_ctor_get(v_r_2413_, 4);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_r_2413_, 3);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_r_2413_, 2);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_r_2413_, 1);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_r_2413_, 0);
lean_dec(v_unused_2497_);
v___x_2487_ = v_r_2413_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v_r_2413_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 4, v___x_2485_);
lean_ctor_set(v___x_2487_, 3, v_l_2424_);
lean_ctor_set(v___x_2487_, 2, v_v_2423_);
lean_ctor_set(v___x_2487_, 1, v_k_2422_);
lean_ctor_set(v___x_2487_, 0, v___x_2481_);
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_l_2424_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v___x_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2505_; 
v_l_2505_ = lean_ctor_get(v_impl_2418_, 3);
lean_inc(v_l_2505_);
if (lean_obj_tag(v_l_2505_) == 0)
{
lean_object* v_r_2506_; lean_object* v_k_2507_; lean_object* v_v_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2519_; 
v_r_2506_ = lean_ctor_get(v_impl_2418_, 4);
v_k_2507_ = lean_ctor_get(v_impl_2418_, 1);
v_v_2508_ = lean_ctor_get(v_impl_2418_, 2);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_impl_2418_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2520_ = lean_ctor_get(v_impl_2418_, 3);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_impl_2418_, 0);
lean_dec(v_unused_2521_);
v___x_2510_ = v_impl_2418_;
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_r_2506_);
lean_inc(v_v_2508_);
lean_inc(v_k_2507_);
lean_dec(v_impl_2418_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2512_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2506_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 3, v_r_2506_);
lean_ctor_set(v___x_2510_, 2, v_v_2411_);
lean_ctor_set(v___x_2510_, 1, v_k_2410_);
lean_ctor_set(v___x_2510_, 0, v___x_2419_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_r_2506_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_r_2506_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v___x_2514_);
lean_ctor_set(v___x_2415_, 3, v_l_2505_);
lean_ctor_set(v___x_2415_, 2, v_v_2508_);
lean_ctor_set(v___x_2415_, 1, v_k_2507_);
lean_ctor_set(v___x_2415_, 0, v___x_2512_);
v___x_2516_ = v___x_2415_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_k_2507_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_v_2508_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_l_2505_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_r_2522_; 
v_r_2522_ = lean_ctor_get(v_impl_2418_, 4);
lean_inc(v_r_2522_);
if (lean_obj_tag(v_r_2522_) == 0)
{
lean_object* v_k_2523_; lean_object* v_v_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2547_; 
v_k_2523_ = lean_ctor_get(v_impl_2418_, 1);
v_v_2524_ = lean_ctor_get(v_impl_2418_, 2);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_impl_2418_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; 
v_unused_2548_ = lean_ctor_get(v_impl_2418_, 4);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_impl_2418_, 3);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_impl_2418_, 0);
lean_dec(v_unused_2550_);
v___x_2526_ = v_impl_2418_;
v_isShared_2527_ = v_isSharedCheck_2547_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_v_2524_);
lean_inc(v_k_2523_);
lean_dec(v_impl_2418_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2547_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_k_2528_; lean_object* v_v_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2543_; 
v_k_2528_ = lean_ctor_get(v_r_2522_, 1);
v_v_2529_ = lean_ctor_get(v_r_2522_, 2);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_r_2522_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; lean_object* v_unused_2545_; lean_object* v_unused_2546_; 
v_unused_2544_ = lean_ctor_get(v_r_2522_, 4);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_r_2522_, 3);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_r_2522_, 0);
lean_dec(v_unused_2546_);
v___x_2531_ = v_r_2522_;
v_isShared_2532_ = v_isSharedCheck_2543_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_v_2529_);
lean_inc(v_k_2528_);
lean_dec(v_r_2522_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2543_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_unsigned_to_nat(3u);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v_l_2505_);
lean_ctor_set(v___x_2531_, 3, v_l_2505_);
lean_ctor_set(v___x_2531_, 2, v_v_2524_);
lean_ctor_set(v___x_2531_, 1, v_k_2523_);
lean_ctor_set(v___x_2531_, 0, v___x_2419_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_k_2523_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_v_2524_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_l_2505_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_l_2505_);
v___x_2535_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 4, v_l_2505_);
lean_ctor_set(v___x_2526_, 2, v_v_2411_);
lean_ctor_set(v___x_2526_, 1, v_k_2410_);
lean_ctor_set(v___x_2526_, 0, v___x_2419_);
v___x_2537_ = v___x_2526_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_l_2505_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_l_2505_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v___x_2537_);
lean_ctor_set(v___x_2415_, 3, v___x_2535_);
lean_ctor_set(v___x_2415_, 2, v_v_2529_);
lean_ctor_set(v___x_2415_, 1, v_k_2528_);
lean_ctor_set(v___x_2415_, 0, v___x_2533_);
v___x_2539_ = v___x_2415_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_2528_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_2529_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_unsigned_to_nat(2u);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_r_2522_);
lean_ctor_set(v___x_2415_, 3, v_impl_2418_);
lean_ctor_set(v___x_2415_, 0, v___x_2551_);
v___x_2553_ = v___x_2415_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_r_2522_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2556_; 
lean_dec(v_v_2411_);
lean_dec(v_k_2410_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 2, v_v_2407_);
lean_ctor_set(v___x_2415_, 1, v_k_2406_);
v___x_2556_ = v___x_2415_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_2409_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_k_2406_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_v_2407_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_l_2412_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_r_2413_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
default: 
{
lean_object* v_impl_2558_; lean_object* v___x_2559_; 
lean_dec(v_size_2409_);
v_impl_2558_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_2406_, v_v_2407_, v_r_2413_);
v___x_2559_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2412_) == 0)
{
lean_object* v_size_2560_; lean_object* v_size_2561_; lean_object* v_k_2562_; lean_object* v_v_2563_; lean_object* v_l_2564_; lean_object* v_r_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v_size_2560_ = lean_ctor_get(v_l_2412_, 0);
v_size_2561_ = lean_ctor_get(v_impl_2558_, 0);
lean_inc(v_size_2561_);
v_k_2562_ = lean_ctor_get(v_impl_2558_, 1);
lean_inc(v_k_2562_);
v_v_2563_ = lean_ctor_get(v_impl_2558_, 2);
lean_inc(v_v_2563_);
v_l_2564_ = lean_ctor_get(v_impl_2558_, 3);
lean_inc(v_l_2564_);
v_r_2565_ = lean_ctor_get(v_impl_2558_, 4);
lean_inc(v_r_2565_);
v___x_2566_ = lean_unsigned_to_nat(3u);
v___x_2567_ = lean_nat_mul(v___x_2566_, v_size_2560_);
v___x_2568_ = lean_nat_dec_lt(v___x_2567_, v_size_2561_);
lean_dec(v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_dec(v_r_2565_);
lean_dec(v_l_2564_);
lean_dec(v_v_2563_);
lean_dec(v_k_2562_);
v___x_2569_ = lean_nat_add(v___x_2559_, v_size_2560_);
v___x_2570_ = lean_nat_add(v___x_2569_, v_size_2561_);
lean_dec(v_size_2561_);
lean_dec(v___x_2569_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_impl_2558_);
lean_ctor_set(v___x_2415_, 0, v___x_2570_);
v___x_2572_ = v___x_2415_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_l_2412_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_impl_2558_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
else
{
lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2637_; 
v_isSharedCheck_2637_ = !lean_is_exclusive(v_impl_2558_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; 
v_unused_2638_ = lean_ctor_get(v_impl_2558_, 4);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_impl_2558_, 3);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_impl_2558_, 2);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_impl_2558_, 1);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_impl_2558_, 0);
lean_dec(v_unused_2642_);
v___x_2575_ = v_impl_2558_;
v_isShared_2576_ = v_isSharedCheck_2637_;
goto v_resetjp_2574_;
}
else
{
lean_dec(v_impl_2558_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2637_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v_size_2577_; lean_object* v_k_2578_; lean_object* v_v_2579_; lean_object* v_l_2580_; lean_object* v_r_2581_; lean_object* v_size_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v_size_2577_ = lean_ctor_get(v_l_2564_, 0);
v_k_2578_ = lean_ctor_get(v_l_2564_, 1);
v_v_2579_ = lean_ctor_get(v_l_2564_, 2);
v_l_2580_ = lean_ctor_get(v_l_2564_, 3);
v_r_2581_ = lean_ctor_get(v_l_2564_, 4);
v_size_2582_ = lean_ctor_get(v_r_2565_, 0);
v___x_2583_ = lean_unsigned_to_nat(2u);
v___x_2584_ = lean_nat_mul(v___x_2583_, v_size_2582_);
v___x_2585_ = lean_nat_dec_lt(v_size_2577_, v___x_2584_);
lean_dec(v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2613_; 
lean_inc(v_r_2581_);
lean_inc(v_l_2580_);
lean_inc(v_v_2579_);
lean_inc(v_k_2578_);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_l_2564_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; lean_object* v_unused_2615_; lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; 
v_unused_2614_ = lean_ctor_get(v_l_2564_, 4);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v_l_2564_, 3);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_l_2564_, 2);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_l_2564_, 1);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_l_2564_, 0);
lean_dec(v_unused_2618_);
v___x_2587_ = v_l_2564_;
v_isShared_2588_ = v_isSharedCheck_2613_;
goto v_resetjp_2586_;
}
else
{
lean_dec(v_l_2564_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2613_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2603_; 
v___x_2589_ = lean_nat_add(v___x_2559_, v_size_2560_);
v___x_2590_ = lean_nat_add(v___x_2589_, v_size_2561_);
lean_dec(v_size_2561_);
if (lean_obj_tag(v_l_2580_) == 0)
{
lean_object* v_size_2611_; 
v_size_2611_ = lean_ctor_get(v_l_2580_, 0);
lean_inc(v_size_2611_);
v___y_2603_ = v_size_2611_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_unsigned_to_nat(0u);
v___y_2603_ = v___x_2612_;
goto v___jp_2602_;
}
v___jp_2591_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_nat_add(v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec(v___y_2593_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 4, v_r_2565_);
lean_ctor_set(v___x_2587_, 3, v_r_2581_);
lean_ctor_set(v___x_2587_, 2, v_v_2563_);
lean_ctor_set(v___x_2587_, 1, v_k_2562_);
lean_ctor_set(v___x_2587_, 0, v___x_2595_);
v___x_2597_ = v___x_2587_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2562_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2563_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_r_2581_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2565_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v___x_2597_);
lean_ctor_set(v___x_2575_, 3, v___y_2592_);
lean_ctor_set(v___x_2575_, 2, v_v_2579_);
lean_ctor_set(v___x_2575_, 1, v_k_2578_);
lean_ctor_set(v___x_2575_, 0, v___x_2590_);
v___x_2599_ = v___x_2575_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v___y_2592_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_nat_add(v___x_2589_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec(v___x_2589_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_l_2580_);
lean_ctor_set(v___x_2415_, 0, v___x_2604_);
v___x_2606_ = v___x_2415_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_l_2412_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_l_2580_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_nat_add(v___x_2559_, v_size_2582_);
if (lean_obj_tag(v_r_2581_) == 0)
{
lean_object* v_size_2608_; 
v_size_2608_ = lean_ctor_get(v_r_2581_, 0);
lean_inc(v_size_2608_);
v___y_2592_ = v___x_2606_;
v___y_2593_ = v___x_2607_;
v___y_2594_ = v_size_2608_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___y_2592_ = v___x_2606_;
v___y_2593_ = v___x_2607_;
v___y_2594_ = v___x_2609_;
goto v___jp_2591_;
}
}
}
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_del_object(v___x_2415_);
v___x_2619_ = lean_nat_add(v___x_2559_, v_size_2560_);
v___x_2620_ = lean_nat_add(v___x_2619_, v_size_2561_);
lean_dec(v_size_2561_);
v___x_2621_ = lean_nat_add(v___x_2619_, v_size_2577_);
lean_dec(v___x_2619_);
lean_inc_ref(v_l_2412_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2564_);
lean_ctor_set(v___x_2575_, 3, v_l_2412_);
lean_ctor_set(v___x_2575_, 2, v_v_2411_);
lean_ctor_set(v___x_2575_, 1, v_k_2410_);
lean_ctor_set(v___x_2575_, 0, v___x_2621_);
v___x_2623_ = v___x_2575_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_l_2412_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_l_2564_);
v___x_2623_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_isSharedCheck_2630_ = !lean_is_exclusive(v_l_2412_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; 
v_unused_2631_ = lean_ctor_get(v_l_2412_, 4);
lean_dec(v_unused_2631_);
v_unused_2632_ = lean_ctor_get(v_l_2412_, 3);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2412_, 2);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2412_, 1);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_l_2412_, 0);
lean_dec(v_unused_2635_);
v___x_2625_ = v_l_2412_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_dec(v_l_2412_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 4, v_r_2565_);
lean_ctor_set(v___x_2625_, 3, v___x_2623_);
lean_ctor_set(v___x_2625_, 2, v_v_2563_);
lean_ctor_set(v___x_2625_, 1, v_k_2562_);
lean_ctor_set(v___x_2625_, 0, v___x_2620_);
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2562_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2563_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_r_2565_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2643_; 
v_l_2643_ = lean_ctor_get(v_impl_2558_, 3);
lean_inc(v_l_2643_);
if (lean_obj_tag(v_l_2643_) == 0)
{
lean_object* v_r_2644_; lean_object* v_k_2645_; lean_object* v_v_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2669_; 
v_r_2644_ = lean_ctor_get(v_impl_2558_, 4);
v_k_2645_ = lean_ctor_get(v_impl_2558_, 1);
v_v_2646_ = lean_ctor_get(v_impl_2558_, 2);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_impl_2558_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; lean_object* v_unused_2671_; 
v_unused_2670_ = lean_ctor_get(v_impl_2558_, 3);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_impl_2558_, 0);
lean_dec(v_unused_2671_);
v___x_2648_ = v_impl_2558_;
v_isShared_2649_ = v_isSharedCheck_2669_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_r_2644_);
lean_inc(v_v_2646_);
lean_inc(v_k_2645_);
lean_dec(v_impl_2558_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2669_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_k_2650_; lean_object* v_v_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2665_; 
v_k_2650_ = lean_ctor_get(v_l_2643_, 1);
v_v_2651_ = lean_ctor_get(v_l_2643_, 2);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_l_2643_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; lean_object* v_unused_2667_; lean_object* v_unused_2668_; 
v_unused_2666_ = lean_ctor_get(v_l_2643_, 4);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_l_2643_, 3);
lean_dec(v_unused_2667_);
v_unused_2668_ = lean_ctor_get(v_l_2643_, 0);
lean_dec(v_unused_2668_);
v___x_2653_ = v_l_2643_;
v_isShared_2654_ = v_isSharedCheck_2665_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_v_2651_);
lean_inc(v_k_2650_);
lean_dec(v_l_2643_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2665_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2655_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2644_, 2);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 4, v_r_2644_);
lean_ctor_set(v___x_2653_, 3, v_r_2644_);
lean_ctor_set(v___x_2653_, 2, v_v_2411_);
lean_ctor_set(v___x_2653_, 1, v_k_2410_);
lean_ctor_set(v___x_2653_, 0, v___x_2559_);
v___x_2657_ = v___x_2653_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_r_2644_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v_r_2644_);
v___x_2657_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2659_; 
lean_inc(v_r_2644_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 3, v_r_2644_);
lean_ctor_set(v___x_2648_, 0, v___x_2559_);
v___x_2659_ = v___x_2648_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_k_2645_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_v_2646_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_r_2644_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_r_2644_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v___x_2659_);
lean_ctor_set(v___x_2415_, 3, v___x_2657_);
lean_ctor_set(v___x_2415_, 2, v_v_2651_);
lean_ctor_set(v___x_2415_, 1, v_k_2650_);
lean_ctor_set(v___x_2415_, 0, v___x_2655_);
v___x_2661_ = v___x_2415_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_k_2650_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_v_2651_);
lean_ctor_set(v_reuseFailAlloc_2662_, 3, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2662_, 4, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
else
{
lean_object* v_r_2672_; 
v_r_2672_ = lean_ctor_get(v_impl_2558_, 4);
lean_inc(v_r_2672_);
if (lean_obj_tag(v_r_2672_) == 0)
{
lean_object* v_k_2673_; lean_object* v_v_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2685_; 
v_k_2673_ = lean_ctor_get(v_impl_2558_, 1);
v_v_2674_ = lean_ctor_get(v_impl_2558_, 2);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_impl_2558_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2686_ = lean_ctor_get(v_impl_2558_, 4);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_impl_2558_, 3);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_impl_2558_, 0);
lean_dec(v_unused_2688_);
v___x_2676_ = v_impl_2558_;
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_v_2674_);
lean_inc(v_k_2673_);
lean_dec(v_impl_2558_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_unsigned_to_nat(3u);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 4, v_l_2643_);
lean_ctor_set(v___x_2676_, 2, v_v_2411_);
lean_ctor_set(v___x_2676_, 1, v_k_2410_);
lean_ctor_set(v___x_2676_, 0, v___x_2559_);
v___x_2680_ = v___x_2676_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_l_2643_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_l_2643_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_r_2672_);
lean_ctor_set(v___x_2415_, 3, v___x_2680_);
lean_ctor_set(v___x_2415_, 2, v_v_2674_);
lean_ctor_set(v___x_2415_, 1, v_k_2673_);
lean_ctor_set(v___x_2415_, 0, v___x_2678_);
v___x_2682_ = v___x_2415_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2673_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2674_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_r_2672_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = lean_unsigned_to_nat(2u);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_impl_2558_);
lean_ctor_set(v___x_2415_, 3, v_r_2672_);
lean_ctor_set(v___x_2415_, 0, v___x_2689_);
v___x_2691_ = v___x_2415_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_k_2410_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_v_2411_);
lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_r_2672_);
lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_impl_2558_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
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
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v_k_2406_);
lean_ctor_set(v___x_2695_, 2, v_v_2407_);
lean_ctor_set(v___x_2695_, 3, v_t_2408_);
lean_ctor_set(v___x_2695_, 4, v_t_2408_);
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(size_t v_sz_2696_, size_t v_i_2697_, lean_object* v_bs_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_usize_dec_lt(v_i_2697_, v_sz_2696_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_bs_2698_);
return v___x_2700_;
}
else
{
lean_object* v_v_2701_; lean_object* v___x_2702_; lean_object* v_bs_x27_2703_; lean_object* v_a_2705_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2776_; 
v_v_2701_ = lean_array_uget(v_bs_2698_, v_i_2697_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v_bs_x27_2703_ = lean_array_uset(v_bs_2698_, v_i_2697_, v___x_2702_);
v___x_2710_ = lean_array_get_size(v_v_2701_);
v___x_2711_ = lean_unsigned_to_nat(4u);
v___x_2776_ = lean_nat_dec_eq(v___x_2710_, v___x_2711_);
if (v___x_2776_ == 0)
{
if (v___x_2699_ == 0)
{
goto v___jp_2712_;
}
else
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = lean_unsigned_to_nat(5u);
v___x_2778_ = lean_nat_dec_eq(v___x_2710_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_v_2701_);
v___x_2779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2780_ = l_Nat_reprFast(v___x_2710_);
v___x_2781_ = lean_string_append(v___x_2779_, v___x_2780_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
else
{
goto v___jp_2712_;
}
}
}
else
{
goto v___jp_2712_;
}
v___jp_2704_:
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2697_, v___x_2706_);
v___x_2708_ = lean_array_uset(v_bs_x27_2703_, v_i_2697_, v_a_2705_);
v_i_2697_ = v___x_2707_;
v_bs_2698_ = v___x_2708_;
goto _start;
}
v___jp_2712_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_array_fget_borrowed(v_v_2701_, v___x_2702_);
lean_inc(v___x_2713_);
v___x_2714_ = l_Lean_Json_getNat_x3f(v___x_2713_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_v_2701_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_a_2723_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2723_);
lean_dec_ref(v___x_2714_);
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_array_fget_borrowed(v_v_2701_, v___x_2724_);
lean_inc(v___x_2725_);
v___x_2726_ = l_Lean_Json_getNat_x3f(v___x_2725_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2723_);
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_v_2701_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_a_2735_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2726_);
v___x_2736_ = lean_unsigned_to_nat(2u);
v___x_2737_ = lean_array_fget_borrowed(v_v_2701_, v___x_2736_);
lean_inc(v___x_2737_);
v___x_2738_ = l_Lean_Json_getNat_x3f(v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_a_2735_);
lean_dec(v_a_2723_);
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_v_2701_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2747_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2738_);
v___x_2748_ = lean_unsigned_to_nat(3u);
v___x_2749_ = lean_array_fget_borrowed(v_v_2701_, v___x_2748_);
lean_inc(v___x_2749_);
v___x_2750_ = l_Lean_Json_getNat_x3f(v___x_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2735_);
lean_dec(v_a_2723_);
lean_dec_ref(v_bs_x27_2703_);
lean_dec(v_v_2701_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2750_);
v___x_2760_ = lean_unsigned_to_nat(5u);
v___x_2761_ = lean_nat_dec_eq(v___x_2710_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v_v_2701_);
v___x_2762_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
v___x_2763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2723_);
lean_ctor_set(v___x_2763_, 1, v_a_2735_);
lean_ctor_set(v___x_2763_, 2, v_a_2747_);
lean_ctor_set(v___x_2763_, 3, v_a_2759_);
lean_ctor_set(v___x_2763_, 4, v___x_2762_);
v_a_2705_ = v___x_2763_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_array_fget(v_v_2701_, v___x_2711_);
lean_dec(v_v_2701_);
v___x_2765_ = l_Lean_Json_getStr_x3f(v___x_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2759_);
lean_dec(v_a_2747_);
lean_dec(v_a_2735_);
lean_dec(v_a_2723_);
lean_dec_ref(v_bs_x27_2703_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2765_);
v___x_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2723_);
lean_ctor_set(v___x_2775_, 1, v_a_2735_);
lean_ctor_set(v___x_2775_, 2, v_a_2747_);
lean_ctor_set(v___x_2775_, 3, v_a_2759_);
lean_ctor_set(v___x_2775_, 4, v_a_2774_);
v_a_2705_ = v___x_2775_;
goto v___jp_2704_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1___boxed(lean_object* v_sz_2783_, lean_object* v_i_2784_, lean_object* v_bs_2785_){
_start:
{
size_t v_sz_boxed_2786_; size_t v_i_boxed_2787_; lean_object* v_res_2788_; 
v_sz_boxed_2786_ = lean_unbox_usize(v_sz_2783_);
lean_dec(v_sz_2783_);
v_i_boxed_2787_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_boxed_2786_, v_i_boxed_2787_, v_bs_2785_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2789_, size_t v_i_2790_, lean_object* v_bs_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = lean_usize_dec_lt(v_i_2790_, v_sz_2789_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_bs_2791_);
return v___x_2793_;
}
else
{
lean_object* v_v_2794_; lean_object* v___x_2795_; 
v_v_2794_ = lean_array_uget_borrowed(v_bs_2791_, v_i_2790_);
lean_inc(v_v_2794_);
v___x_2795_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__3(v_v_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_bs_2791_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v_bs_x27_2806_; size_t v___x_2807_; size_t v___x_2808_; lean_object* v___x_2809_; 
v_a_2804_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2804_);
lean_dec_ref(v___x_2795_);
v___x_2805_ = lean_unsigned_to_nat(0u);
v_bs_x27_2806_ = lean_array_uset(v_bs_2791_, v_i_2790_, v___x_2805_);
v___x_2807_ = ((size_t)1ULL);
v___x_2808_ = lean_usize_add(v_i_2790_, v___x_2807_);
v___x_2809_ = lean_array_uset(v_bs_x27_2806_, v_i_2790_, v_a_2804_);
v_i_2790_ = v___x_2808_;
v_bs_2791_ = v___x_2809_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_2811_, lean_object* v_i_2812_, lean_object* v_bs_2813_){
_start:
{
size_t v_sz_boxed_2814_; size_t v_i_boxed_2815_; lean_object* v_res_2816_; 
v_sz_boxed_2814_ = lean_unbox_usize(v_sz_2811_);
lean_dec(v_sz_2811_);
v_i_boxed_2815_ = lean_unbox_usize(v_i_2812_);
lean_dec(v_i_2812_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_2814_, v_i_boxed_2815_, v_bs_2813_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_2817_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 4)
{
lean_object* v_elems_2818_; size_t v_sz_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v_elems_2818_ = lean_ctor_get(v_x_2817_, 0);
lean_inc_ref(v_elems_2818_);
lean_dec_ref(v_x_2817_);
v_sz_2819_ = lean_array_size(v_elems_2818_);
v___x_2820_ = ((size_t)0ULL);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2819_, v___x_2820_, v_elems_2818_);
return v___x_2821_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2822_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_2823_ = lean_unsigned_to_nat(80u);
v___x_2824_ = l_Lean_Json_pretty(v_x_2817_, v___x_2823_);
v___x_2825_ = lean_string_append(v___x_2822_, v___x_2824_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_2827_ = lean_string_append(v___x_2825_, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(lean_object* v_j_2829_, lean_object* v_k_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = l_Lean_Json_getObjValD(v_j_2829_, v_k_2830_);
v___x_2832_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0_spec__1(v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0___boxed(lean_object* v_j_2833_, lean_object* v_k_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_j_2833_, v_k_2834_);
lean_dec_ref(v_k_2834_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(lean_object* v_init_2836_, lean_object* v_x_2837_){
_start:
{
if (lean_obj_tag(v_x_2837_) == 0)
{
lean_object* v_k_2838_; lean_object* v_v_2839_; lean_object* v_l_2840_; lean_object* v_r_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_3001_; 
v_k_2838_ = lean_ctor_get(v_x_2837_, 1);
v_v_2839_ = lean_ctor_get(v_x_2837_, 2);
v_l_2840_ = lean_ctor_get(v_x_2837_, 3);
v_r_2841_ = lean_ctor_get(v_x_2837_, 4);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_x_2837_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v_x_2837_, 0);
lean_dec(v_unused_3002_);
v___x_2843_ = v_x_2837_;
v_isShared_2844_ = v_isSharedCheck_3001_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_r_2841_);
lean_inc(v_l_2840_);
lean_inc(v_v_2839_);
lean_inc(v_k_2838_);
lean_dec(v_x_2837_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_3001_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v_init_2836_, v_l_2840_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
lean_dec(v_k_2838_);
return v___x_2845_;
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_3000_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_3000_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_3000_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Json_parse(v_k_2838_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___x_2850_);
v___x_2860_ = l_Lean_Lsp_RefIdent_fromJson_x3f(v_a_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v_definition_x3f_2871_; lean_object* v_a_2899_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_a_2869_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2860_);
v___x_2903_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
lean_inc(v_v_2839_);
v___x_2904_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__3(v_v_2839_, v___x_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
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
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2999_; 
v_a_2913_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2915_ = v___x_2904_;
v_isShared_2916_ = v_isSharedCheck_2999_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2904_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2999_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
if (lean_obj_tag(v_a_2913_) == 0)
{
lean_object* v___x_2917_; 
lean_del_object(v___x_2915_);
lean_del_object(v___x_2848_);
lean_del_object(v___x_2843_);
v___x_2917_ = lean_box(0);
v_definition_x3f_2871_ = v___x_2917_;
goto v___jp_2870_;
}
else
{
lean_object* v_val_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2990_; 
v_val_2918_ = lean_ctor_get(v_a_2913_, 0);
lean_inc(v_val_2918_);
lean_dec_ref(v_a_2913_);
v___x_2919_ = lean_array_get_size(v_val_2918_);
v___x_2920_ = lean_unsigned_to_nat(4u);
v___x_2990_ = lean_nat_dec_eq(v___x_2919_, v___x_2920_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = lean_unsigned_to_nat(5u);
v___x_2992_ = lean_nat_dec_eq(v___x_2919_, v___x_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_dec(v_val_2918_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v___x_2993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRefInfo___lam__0___closed__0));
v___x_2994_ = l_Nat_reprFast(v___x_2919_);
v___x_2995_ = lean_string_append(v___x_2993_, v___x_2994_);
lean_dec_ref(v___x_2994_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2995_);
v___x_2997_ = v___x_2915_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
lean_del_object(v___x_2915_);
goto v___jp_2921_;
}
}
else
{
lean_del_object(v___x_2915_);
goto v___jp_2921_;
}
v___jp_2921_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = lean_array_fget_borrowed(v_val_2918_, v___x_2922_);
lean_inc(v___x_2923_);
v___x_2924_ = l_Lean_Json_getNat_x3f(v___x_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_val_2918_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
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
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_a_2933_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2924_);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_array_fget_borrowed(v_val_2918_, v___x_2934_);
lean_inc(v___x_2935_);
v___x_2936_ = l_Lean_Json_getNat_x3f(v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_a_2933_);
lean_dec(v_val_2918_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2936_);
v___x_2946_ = lean_unsigned_to_nat(2u);
v___x_2947_ = lean_array_fget_borrowed(v_val_2918_, v___x_2946_);
lean_inc(v___x_2947_);
v___x_2948_ = l_Lean_Json_getNat_x3f(v___x_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_a_2945_);
lean_dec(v_a_2933_);
lean_dec(v_val_2918_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
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
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2957_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2948_);
v___x_2958_ = lean_unsigned_to_nat(3u);
v___x_2959_ = lean_array_fget_borrowed(v_val_2918_, v___x_2958_);
lean_inc(v___x_2959_);
v___x_2960_ = l_Lean_Json_getNat_x3f(v___x_2959_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_a_2957_);
lean_dec(v_a_2945_);
lean_dec(v_a_2933_);
lean_dec(v_val_2918_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_a_2969_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2960_);
v___x_2970_ = lean_unsigned_to_nat(5u);
v___x_2971_ = lean_nat_dec_eq(v___x_2919_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_val_2918_);
v___x_2972_ = ((lean_object*)(l_Lean_Lsp_instInhabitedImportInfo_default___closed__0));
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 4, v___x_2972_);
lean_ctor_set(v___x_2843_, 3, v_a_2969_);
lean_ctor_set(v___x_2843_, 2, v_a_2957_);
lean_ctor_set(v___x_2843_, 1, v_a_2945_);
lean_ctor_set(v___x_2843_, 0, v_a_2933_);
v___x_2974_ = v___x_2843_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2933_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_a_2969_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
v_a_2899_ = v___x_2974_;
goto v___jp_2898_;
}
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_array_fget(v_val_2918_, v___x_2920_);
lean_dec(v_val_2918_);
v___x_2977_ = l_Lean_Json_getStr_x3f(v___x_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_a_2969_);
lean_dec(v_a_2957_);
lean_dec(v_a_2945_);
lean_dec(v_a_2933_);
lean_dec(v_a_2869_);
lean_del_object(v___x_2848_);
lean_dec(v_a_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_r_2841_);
lean_dec(v_v_2839_);
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2977_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 4, v_a_2986_);
lean_ctor_set(v___x_2843_, 3, v_a_2969_);
lean_ctor_set(v___x_2843_, 2, v_a_2957_);
lean_ctor_set(v___x_2843_, 1, v_a_2945_);
lean_ctor_set(v___x_2843_, 0, v_a_2933_);
v___x_2988_ = v___x_2843_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2933_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_a_2969_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_a_2986_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v_a_2899_ = v___x_2988_;
goto v___jp_2898_;
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
v___jp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v___x_2873_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__0(v_v_2839_, v___x_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_definition_x3f_2871_);
lean_dec(v_a_2869_);
lean_dec(v_a_2846_);
lean_dec(v_r_2841_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v_a_2882_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2873_);
v_sz_2883_ = lean_array_size(v_a_2882_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__1(v_sz_2883_, v___x_2884_, v_a_2882_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_definition_x3f_2871_);
lean_dec(v_a_2869_);
lean_dec(v_a_2846_);
lean_dec(v_r_2841_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2885_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v_definition_x3f_2871_);
lean_ctor_set(v___x_2895_, 1, v_a_2894_);
v___x_2896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_a_2869_, v___x_2895_, v_a_2846_);
v_init_2836_ = v___x_2896_;
v_x_2837_ = v_r_2841_;
goto _start;
}
}
}
v___jp_2898_:
{
lean_object* v___x_2901_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v_a_2899_);
v___x_2901_ = v___x_2848_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_definition_x3f_2871_ = v___x_2901_;
goto v___jp_2870_;
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
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_init_2836_);
return v___x_3003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(lean_object* v_j_3004_, lean_object* v_k_3005_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = l_Lean_Json_getObjValD(v_j_3004_, v_k_3005_);
v___x_3007_ = l_Lean_Json_getObj_x3f(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
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
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v___x_3007_);
v___x_3017_ = lean_box(1);
v___x_3018_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__4(v___x_3017_, v_a_3016_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0___boxed(lean_object* v_j_3019_, lean_object* v_k_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_j_3019_, v_k_3020_);
lean_dec_ref(v_k_3020_);
return v_res_3021_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = 1;
v___x_3028_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__1));
v___x_3029_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3028_, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3031_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__2);
v___x_3032_ = lean_string_append(v___x_3031_, v___x_3030_);
return v___x_3032_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__9);
v___x_3034_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3035_ = lean_string_append(v___x_3034_, v___x_3033_);
return v___x_3035_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3037_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__4);
v___x_3038_ = lean_string_append(v___x_3037_, v___x_3036_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = 1;
v___x_3043_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__7));
v___x_3044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3043_, v___x_3042_);
return v___x_3044_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__8);
v___x_3046_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3047_ = lean_string_append(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3049_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__9);
v___x_3050_ = lean_string_append(v___x_3049_, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = 1;
v___x_3055_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__12));
v___x_3056_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__13);
v___x_3058_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__3);
v___x_3059_ = lean_string_append(v___x_3058_, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3061_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__14);
v___x_3062_ = lean_string_append(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson(lean_object* v_json_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
lean_inc(v_json_3063_);
v___x_3065_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__0(v_json_3063_, v___x_3064_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_json_3063_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3075_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3075_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3070_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__5);
v___x_3071_ = lean_string_append(v___x_3070_, v_a_3066_);
lean_dec(v_a_3066_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3071_);
v___x_3073_ = v___x_3068_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_json_3063_);
v_a_3076_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3065_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3065_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 0);
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3065_);
v___x_3085_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
lean_inc(v_json_3063_);
v___x_3086_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0(v_json_3063_, v___x_3085_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3084_);
lean_dec(v_json_3063_);
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3091_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__10);
v___x_3092_ = lean_string_append(v___x_3091_, v_a_3087_);
lean_dec(v_a_3087_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3092_);
v___x_3094_ = v___x_3089_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_a_3084_);
lean_dec(v_json_3063_);
v_a_3097_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3086_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3086_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 0);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3105_);
lean_dec_ref(v___x_3086_);
v___x_3106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1(v_json_3063_, v___x_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_3105_);
lean_dec(v_a_3084_);
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
v___x_3112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__15);
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
lean_dec(v_a_3105_);
lean_dec(v_a_3084_);
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
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_a_3126_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3128_ = v___x_3107_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3107_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3084_);
lean_ctor_set(v___x_3130_, 1, v_a_3105_);
lean_ctor_set(v___x_3130_, 2, v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2(lean_object* v_00_u03b2_3135_, lean_object* v_k_3136_, lean_object* v_v_3137_, lean_object* v_t_3138_, lean_object* v_hl_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__0_spec__2___redArg(v_k_3136_, v_v_3137_, v_t_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6(lean_object* v_00_u03b2_3141_, lean_object* v_k_3142_, lean_object* v_v_3143_, lean_object* v_t_3144_, lean_object* v_hl_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson_spec__1_spec__6___redArg(v_k_3142_, v_v_3143_, v_t_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(lean_object* v_init_3149_, lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 0)
{
lean_object* v_k_3151_; lean_object* v_v_3152_; lean_object* v_l_3153_; lean_object* v_r_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_k_3151_ = lean_ctor_get(v_x_3150_, 1);
v_v_3152_ = lean_ctor_get(v_x_3150_, 2);
v_l_3153_ = lean_ctor_get(v_x_3150_, 3);
v_r_3154_ = lean_ctor_get(v_x_3150_, 4);
v___x_3155_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3149_, v_r_3154_);
lean_inc(v_v_3152_);
lean_inc(v_k_3151_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_k_3151_);
lean_ctor_set(v___x_3156_, 1, v_v_3152_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v___x_3155_);
v_init_3149_ = v___x_3157_;
v_x_3150_ = v_l_3153_;
goto _start;
}
else
{
return v_init_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6___boxed(lean_object* v_init_3159_, lean_object* v_x_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v_init_3159_, v_x_3160_);
lean_dec(v_x_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(size_t v_sz_3162_, size_t v_i_3163_, lean_object* v_bs_3164_){
_start:
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_usize_dec_lt(v_i_3163_, v_sz_3162_);
if (v___x_3165_ == 0)
{
return v_bs_3164_;
}
else
{
lean_object* v_v_3166_; lean_object* v___x_3167_; lean_object* v_bs_x27_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v_v_3166_ = lean_array_uget(v_bs_3164_, v_i_3163_);
v___x_3167_ = lean_unsigned_to_nat(0u);
v_bs_x27_3168_ = lean_array_uset(v_bs_3164_, v_i_3163_, v___x_3167_);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3163_, v___x_3169_);
v___x_3171_ = lean_array_uset(v_bs_x27_3168_, v_i_3163_, v_v_3166_);
v_i_3163_ = v___x_3170_;
v_bs_3164_ = v___x_3171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9___boxed(lean_object* v_sz_3173_, lean_object* v_i_3174_, lean_object* v_bs_3175_){
_start:
{
size_t v_sz_boxed_3176_; size_t v_i_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3176_ = lean_unbox_usize(v_sz_3173_);
lean_dec(v_sz_3173_);
v_i_boxed_3177_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_boxed_3176_, v_i_boxed_3177_, v_bs_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(lean_object* v_a_3179_){
_start:
{
size_t v_sz_3180_; size_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_sz_3180_ = lean_array_size(v_a_3179_);
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2_spec__9(v_sz_3180_, v___x_3181_, v_a_3179_);
v___x_3183_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_array_mk(v_a_3184_);
v___x_3186_ = l_Array_toJson___at___00List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1_spec__2(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(lean_object* v_x_3187_){
_start:
{
if (lean_obj_tag(v_x_3187_) == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
else
{
lean_object* v_val_3189_; lean_object* v___x_3190_; 
v_val_3189_ = lean_ctor_get(v_x_3187_, 0);
lean_inc(v_val_3189_);
lean_dec_ref(v_x_3187_);
v___x_3190_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_val_3189_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(size_t v_sz_3191_, size_t v_i_3192_, lean_object* v_bs_3193_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = lean_usize_dec_lt(v_i_3192_, v_sz_3191_);
if (v___x_3194_ == 0)
{
return v_bs_3193_;
}
else
{
lean_object* v_v_3195_; lean_object* v___x_3196_; lean_object* v_bs_x27_3197_; lean_object* v___x_3198_; size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; 
v_v_3195_ = lean_array_uget(v_bs_3193_, v_i_3192_);
v___x_3196_ = lean_unsigned_to_nat(0u);
v_bs_x27_3197_ = lean_array_uset(v_bs_3193_, v_i_3192_, v___x_3196_);
v___x_3198_ = l_List_toJson___at___00Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1_spec__1(v_v_3195_);
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3192_, v___x_3199_);
v___x_3201_ = lean_array_uset(v_bs_x27_3197_, v_i_3192_, v___x_3198_);
v_i_3192_ = v___x_3200_;
v_bs_3193_ = v___x_3201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4___boxed(lean_object* v_sz_3203_, lean_object* v_i_3204_, lean_object* v_bs_3205_){
_start:
{
size_t v_sz_boxed_3206_; size_t v_i_boxed_3207_; lean_object* v_res_3208_; 
v_sz_boxed_3206_ = lean_unbox_usize(v_sz_3203_);
lean_dec(v_sz_3203_);
v_i_boxed_3207_ = lean_unbox_usize(v_i_3204_);
lean_dec(v_i_3204_);
v_res_3208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_boxed_3206_, v_i_boxed_3207_, v_bs_3205_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(lean_object* v_a_3209_){
_start:
{
size_t v_sz_3210_; size_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_sz_3210_ = lean_array_size(v_a_3209_);
v___x_3211_ = ((size_t)0ULL);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3_spec__4(v_sz_3210_, v___x_3211_, v_a_3209_);
v___x_3213_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
if (lean_obj_tag(v_a_3214_) == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = l_List_reverse___redArg(v_a_3215_);
return v___x_3216_;
}
else
{
lean_object* v_head_3217_; lean_object* v_tail_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3228_; 
v_head_3217_ = lean_ctor_get(v_a_3214_, 0);
v_tail_3218_ = lean_ctor_get(v_a_3214_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_3214_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3220_ = v_a_3214_;
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_tail_3218_);
lean_inc(v_head_3217_);
lean_dec(v_a_3214_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3222_ = l_Lean_JsonNumber_fromNat(v_head_3217_);
v___x_3223_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v_a_3215_);
lean_ctor_set(v___x_3220_, 0, v___x_3223_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3215_);
v___x_3225_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
v_a_3214_ = v_tail_3218_;
v_a_3215_ = v___x_3225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(size_t v_sz_3229_, size_t v_i_3230_, lean_object* v_bs_3231_){
_start:
{
uint8_t v___x_3232_; 
v___x_3232_ = lean_usize_dec_lt(v_i_3230_, v_sz_3229_);
if (v___x_3232_ == 0)
{
return v_bs_3231_;
}
else
{
lean_object* v_v_3233_; lean_object* v_startPosLine_3234_; lean_object* v_startPosCharacter_3235_; lean_object* v_endPosLine_3236_; lean_object* v_endPosCharacter_3237_; lean_object* v___x_3238_; lean_object* v_bs_x27_3239_; lean_object* v___y_3241_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_range_3251_; lean_object* v___x_3252_; 
v_v_3233_ = lean_array_uget(v_bs_3231_, v_i_3230_);
v_startPosLine_3234_ = lean_ctor_get(v_v_3233_, 0);
v_startPosCharacter_3235_ = lean_ctor_get(v_v_3233_, 1);
v_endPosLine_3236_ = lean_ctor_get(v_v_3233_, 2);
v_endPosCharacter_3237_ = lean_ctor_get(v_v_3233_, 3);
v___x_3238_ = lean_unsigned_to_nat(0u);
v_bs_x27_3239_ = lean_array_uset(v_bs_3231_, v_i_3230_, v___x_3238_);
v___x_3246_ = lean_box(0);
lean_inc(v_endPosCharacter_3237_);
v___x_3247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_endPosCharacter_3237_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
lean_inc(v_endPosLine_3236_);
v___x_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_endPosLine_3236_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
lean_inc(v_startPosCharacter_3235_);
v___x_3249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_startPosCharacter_3235_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
lean_inc(v_startPosLine_3234_);
v___x_3250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_startPosLine_3234_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v_range_3251_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3250_, v___x_3246_);
v___x_3252_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_v_3233_);
lean_dec(v_v_3233_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = l_List_appendTR___redArg(v_range_3251_, v___x_3246_);
v___y_3241_ = v___x_3253_;
goto v___jp_3240_;
}
else
{
lean_object* v_val_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3263_; 
v_val_3254_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3256_ = v___x_3252_;
v_isShared_3257_ = v_isSharedCheck_3263_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_val_3254_);
lean_dec(v___x_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3263_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set_tag(v___x_3256_, 3);
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_val_3254_);
v___x_3259_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3246_);
v___x_3261_ = l_List_appendTR___redArg(v_range_3251_, v___x_3260_);
v___y_3241_ = v___x_3261_;
goto v___jp_3240_;
}
}
}
v___jp_3240_:
{
size_t v___x_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = ((size_t)1ULL);
v___x_3243_ = lean_usize_add(v_i_3230_, v___x_3242_);
v___x_3244_ = lean_array_uset(v_bs_x27_3239_, v_i_3230_, v___y_3241_);
v_i_3230_ = v___x_3243_;
v_bs_3231_ = v___x_3244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2___boxed(lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_bs_3266_){
_start:
{
size_t v_sz_boxed_3267_; size_t v_i_boxed_3268_; lean_object* v_res_3269_; 
v_sz_boxed_3267_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3268_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_boxed_3267_, v_i_boxed_3268_, v_bs_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
if (lean_obj_tag(v_a_3270_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = l_List_reverse___redArg(v_a_3271_);
return v___x_3272_;
}
else
{
lean_object* v_head_3273_; lean_object* v_snd_3274_; lean_object* v_tail_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3344_; 
v_head_3273_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_head_3273_);
v_snd_3274_ = lean_ctor_get(v_head_3273_, 1);
lean_inc(v_snd_3274_);
v_tail_3275_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; 
v_unused_3345_ = lean_ctor_get(v_a_3270_, 0);
lean_dec(v_unused_3345_);
v___x_3277_ = v_a_3270_;
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_tail_3275_);
lean_dec(v_a_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_fst_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3342_; 
v_fst_3279_ = lean_ctor_get(v_head_3273_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_head_3273_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v_head_3273_, 1);
lean_dec(v_unused_3343_);
v___x_3281_ = v_head_3273_;
v_isShared_3282_ = v_isSharedCheck_3342_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_fst_3279_);
lean_dec(v_head_3273_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3342_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_definition_x3f_3283_; lean_object* v_usages_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3341_; 
v_definition_x3f_3283_ = lean_ctor_get(v_snd_3274_, 0);
v_usages_3284_ = lean_ctor_get(v_snd_3274_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_snd_3274_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3286_ = v_snd_3274_;
v_isShared_3287_ = v_isSharedCheck_3341_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_usages_3284_);
lean_inc(v_definition_x3f_3283_);
lean_dec(v_snd_3274_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3341_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___y_3292_; lean_object* v___y_3315_; 
v___x_3288_ = l_Lean_Lsp_RefIdent_toJson(v_fst_3279_);
v___x_3289_ = l_Lean_Json_compress(v___x_3288_);
v___x_3290_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__0));
if (lean_obj_tag(v_definition_x3f_3283_) == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_box(0);
v___y_3292_ = v___x_3317_;
goto v___jp_3291_;
}
else
{
lean_object* v_val_3318_; lean_object* v_startPosLine_3319_; lean_object* v_startPosCharacter_3320_; lean_object* v_endPosLine_3321_; lean_object* v_endPosCharacter_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v_range_3328_; lean_object* v___x_3329_; 
v_val_3318_ = lean_ctor_get(v_definition_x3f_3283_, 0);
lean_inc(v_val_3318_);
lean_dec_ref(v_definition_x3f_3283_);
v_startPosLine_3319_ = lean_ctor_get(v_val_3318_, 0);
v_startPosCharacter_3320_ = lean_ctor_get(v_val_3318_, 1);
v_endPosLine_3321_ = lean_ctor_get(v_val_3318_, 2);
v_endPosCharacter_3322_ = lean_ctor_get(v_val_3318_, 3);
v___x_3323_ = lean_box(0);
lean_inc(v_endPosCharacter_3322_);
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_endPosCharacter_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
lean_inc(v_endPosLine_3321_);
v___x_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_endPosLine_3321_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
lean_inc(v_startPosCharacter_3320_);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_startPosCharacter_3320_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
lean_inc(v_startPosLine_3319_);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v_startPosLine_3319_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v_range_3328_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__0(v___x_3327_, v___x_3323_);
v___x_3329_ = l_Lean_Lsp_RefInfo_Location_parentDecl_x3f(v_val_3318_);
lean_dec(v_val_3318_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = l_List_appendTR___redArg(v_range_3328_, v___x_3323_);
v___y_3315_ = v___x_3330_;
goto v___jp_3314_;
}
else
{
lean_object* v_val_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3340_; 
v_val_3331_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3333_ = v___x_3329_;
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_val_3331_);
lean_dec(v___x_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set_tag(v___x_3333_, 3);
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_val_3331_);
v___x_3336_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3323_);
v___x_3338_ = l_List_appendTR___redArg(v_range_3328_, v___x_3337_);
v___y_3315_ = v___x_3338_;
goto v___jp_3314_;
}
}
}
}
v___jp_3291_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = l_Option_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__1(v___y_3292_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___x_3293_);
lean_ctor_set(v___x_3281_, 0, v___x_3290_);
v___x_3295_ = v___x_3281_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3290_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; size_t v_sz_3297_; size_t v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3296_ = ((lean_object*)(l_Lean_Lsp_instToJsonRefInfo___lam__3___closed__1));
v_sz_3297_ = lean_array_size(v_usages_3284_);
v___x_3298_ = ((size_t)0ULL);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__2(v_sz_3297_, v___x_3298_, v_usages_3284_);
v___x_3300_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__3(v___x_3299_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v___x_3300_);
lean_ctor_set(v___x_3286_, 0, v___x_3296_);
v___x_3302_ = v___x_3286_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_box(0);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3303_);
lean_ctor_set(v___x_3277_, 0, v___x_3302_);
v___x_3305_ = v___x_3277_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3302_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3295_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Lean_Json_mkObj(v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3289_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
lean_ctor_set(v___x_3309_, 1, v_a_3271_);
v_a_3270_ = v_tail_3275_;
v_a_3271_ = v___x_3309_;
goto _start;
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___y_3315_);
v___y_3292_ = v___x_3316_;
goto v___jp_3291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
if (lean_obj_tag(v_a_3346_) == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = l_List_reverse___redArg(v_a_3347_);
return v___x_3348_;
}
else
{
lean_object* v_head_3349_; lean_object* v_snd_3350_; lean_object* v_tail_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3403_; 
v_head_3349_ = lean_ctor_get(v_a_3346_, 0);
lean_inc(v_head_3349_);
v_snd_3350_ = lean_ctor_get(v_head_3349_, 1);
lean_inc(v_snd_3350_);
v_tail_3351_ = lean_ctor_get(v_a_3346_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_a_3346_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v_a_3346_, 0);
lean_dec(v_unused_3404_);
v___x_3353_ = v_a_3346_;
v_isShared_3354_ = v_isSharedCheck_3403_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_tail_3351_);
lean_dec(v_a_3346_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3403_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_fst_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3401_; 
v_fst_3355_ = lean_ctor_get(v_head_3349_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_head_3349_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_head_3349_, 1);
lean_dec(v_unused_3402_);
v___x_3357_ = v_head_3349_;
v_isShared_3358_ = v_isSharedCheck_3401_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_fst_3355_);
lean_dec(v_head_3349_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3401_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_rangeStartPosLine_3359_; lean_object* v_rangeStartPosCharacter_3360_; lean_object* v_rangeEndPosLine_3361_; lean_object* v_rangeEndPosCharacter_3362_; lean_object* v_selectionRangeStartPosLine_3363_; lean_object* v_selectionRangeStartPosCharacter_3364_; lean_object* v_selectionRangeEndPosLine_3365_; lean_object* v_selectionRangeEndPosCharacter_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
v_rangeStartPosLine_3359_ = lean_ctor_get(v_snd_3350_, 0);
lean_inc(v_rangeStartPosLine_3359_);
v_rangeStartPosCharacter_3360_ = lean_ctor_get(v_snd_3350_, 1);
lean_inc(v_rangeStartPosCharacter_3360_);
v_rangeEndPosLine_3361_ = lean_ctor_get(v_snd_3350_, 2);
lean_inc(v_rangeEndPosLine_3361_);
v_rangeEndPosCharacter_3362_ = lean_ctor_get(v_snd_3350_, 3);
lean_inc(v_rangeEndPosCharacter_3362_);
v_selectionRangeStartPosLine_3363_ = lean_ctor_get(v_snd_3350_, 4);
lean_inc(v_selectionRangeStartPosLine_3363_);
v_selectionRangeStartPosCharacter_3364_ = lean_ctor_get(v_snd_3350_, 5);
lean_inc(v_selectionRangeStartPosCharacter_3364_);
v_selectionRangeEndPosLine_3365_ = lean_ctor_get(v_snd_3350_, 6);
lean_inc(v_selectionRangeEndPosLine_3365_);
v_selectionRangeEndPosCharacter_3366_ = lean_ctor_get(v_snd_3350_, 7);
lean_inc(v_selectionRangeEndPosCharacter_3366_);
lean_dec(v_snd_3350_);
v___x_3367_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosLine_3359_);
v___x_3368_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
v___x_3369_ = l_Lean_JsonNumber_fromNat(v_rangeStartPosCharacter_3360_);
v___x_3370_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosLine_3361_);
v___x_3372_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
v___x_3373_ = l_Lean_JsonNumber_fromNat(v_rangeEndPosCharacter_3362_);
v___x_3374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosLine_3363_);
v___x_3376_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
v___x_3377_ = l_Lean_JsonNumber_fromNat(v_selectionRangeStartPosCharacter_3364_);
v___x_3378_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
v___x_3379_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosLine_3365_);
v___x_3380_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
v___x_3381_ = l_Lean_JsonNumber_fromNat(v_selectionRangeEndPosCharacter_3366_);
v___x_3382_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
v___x_3383_ = lean_unsigned_to_nat(8u);
v___x_3384_ = lean_mk_empty_array_with_capacity(v___x_3383_);
v___x_3385_ = lean_array_push(v___x_3384_, v___x_3368_);
v___x_3386_ = lean_array_push(v___x_3385_, v___x_3370_);
v___x_3387_ = lean_array_push(v___x_3386_, v___x_3372_);
v___x_3388_ = lean_array_push(v___x_3387_, v___x_3374_);
v___x_3389_ = lean_array_push(v___x_3388_, v___x_3376_);
v___x_3390_ = lean_array_push(v___x_3389_, v___x_3378_);
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3380_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3382_);
v___x_3393_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 1, v___x_3393_);
v___x_3395_ = v___x_3357_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_fst_3355_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3397_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v_a_3347_);
lean_ctor_set(v___x_3353_, 0, v___x_3395_);
v___x_3397_ = v___x_3353_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_a_3347_);
v___x_3397_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v_a_3346_ = v_tail_3351_;
v_a_3347_ = v___x_3397_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(lean_object* v_init_3405_, lean_object* v_x_3406_){
_start:
{
if (lean_obj_tag(v_x_3406_) == 0)
{
lean_object* v_k_3407_; lean_object* v_v_3408_; lean_object* v_l_3409_; lean_object* v_r_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_k_3407_ = lean_ctor_get(v_x_3406_, 1);
v_v_3408_ = lean_ctor_get(v_x_3406_, 2);
v_l_3409_ = lean_ctor_get(v_x_3406_, 3);
v_r_3410_ = lean_ctor_get(v_x_3406_, 4);
v___x_3411_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3405_, v_r_3410_);
lean_inc(v_v_3408_);
lean_inc(v_k_3407_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_k_3407_);
lean_ctor_set(v___x_3412_, 1, v_v_3408_);
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___x_3411_);
v_init_3405_ = v___x_3413_;
v_x_3406_ = v_l_3409_;
goto _start;
}
else
{
return v_init_3405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4___boxed(lean_object* v_init_3415_, lean_object* v_x_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v_init_3415_, v_x_3416_);
lean_dec(v_x_3416_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIleanInfoParams_toJson(lean_object* v_x_3418_){
_start:
{
lean_object* v_version_3419_; lean_object* v_references_3420_; lean_object* v_decls_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_version_3419_ = lean_ctor_get(v_x_3418_, 0);
lean_inc(v_version_3419_);
v_references_3420_ = lean_ctor_get(v_x_3418_, 1);
lean_inc(v_references_3420_);
v_decls_3421_ = lean_ctor_get(v_x_3418_, 2);
lean_inc(v_decls_3421_);
lean_dec_ref(v_x_3418_);
v___x_3422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__0));
v___x_3423_ = l_Lean_JsonNumber_fromNat(v_version_3419_);
v___x_3424_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3422_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_box(0);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__6));
v___x_3429_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__4(v___x_3426_, v_references_3420_);
lean_dec(v_references_3420_);
v___x_3430_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__5(v___x_3429_, v___x_3426_);
v___x_3431_ = l_Lean_Json_mkObj(v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3428_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3432_);
lean_ctor_set(v___x_3433_, 1, v___x_3426_);
v___x_3434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIleanInfoParams_fromJson___closed__11));
v___x_3435_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__6(v___x_3426_, v_decls_3421_);
lean_dec(v_decls_3421_);
v___x_3436_ = l_List_mapTR_loop___at___00Lean_Lsp_instToJsonLeanIleanInfoParams_toJson_spec__7(v___x_3435_, v___x_3426_);
v___x_3437_ = l_Lean_Json_mkObj(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3434_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set(v___x_3439_, 1, v___x_3426_);
v___x_3440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v___x_3426_);
v___x_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3433_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3427_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3444_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3442_, v___x_3443_);
v___x_3445_ = l_Lean_Json_mkObj(v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3448_, size_t v_i_3449_, lean_object* v_bs_3450_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3449_, v_sz_3448_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_bs_3450_);
return v___x_3452_;
}
else
{
lean_object* v_v_3453_; lean_object* v___x_3454_; 
v_v_3453_ = lean_array_uget_borrowed(v_bs_3450_, v_i_3449_);
lean_inc(v_v_3453_);
v___x_3454_ = l_Lean_Json_getStr_x3f(v_v_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_bs_3450_);
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3464_; lean_object* v_bs_x27_3465_; size_t v___x_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v_a_3463_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3454_);
v___x_3464_ = lean_unsigned_to_nat(0u);
v_bs_x27_3465_ = lean_array_uset(v_bs_3450_, v_i_3449_, v___x_3464_);
v___x_3466_ = ((size_t)1ULL);
v___x_3467_ = lean_usize_add(v_i_3449_, v___x_3466_);
v___x_3468_ = lean_array_uset(v_bs_x27_3465_, v_i_3449_, v_a_3463_);
v_i_3449_ = v___x_3467_;
v_bs_3450_ = v___x_3468_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3470_, lean_object* v_i_3471_, lean_object* v_bs_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3470_);
lean_dec(v_sz_3470_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3471_);
lean_dec(v_i_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3473_, v_i_boxed_3474_, v_bs_3472_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(lean_object* v_x_3476_){
_start:
{
if (lean_obj_tag(v_x_3476_) == 4)
{
lean_object* v_elems_3477_; size_t v_sz_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v_elems_3477_ = lean_ctor_get(v_x_3476_, 0);
lean_inc_ref(v_elems_3477_);
lean_dec_ref(v_x_3476_);
v_sz_3478_ = lean_array_size(v_elems_3477_);
v___x_3479_ = ((size_t)0ULL);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0_spec__1(v_sz_3478_, v___x_3479_, v_elems_3477_);
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3481_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3482_ = lean_unsigned_to_nat(80u);
v___x_3483_ = l_Lean_Json_pretty(v_x_3476_, v___x_3482_);
v___x_3484_ = lean_string_append(v___x_3481_, v___x_3483_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(lean_object* v_j_3488_, lean_object* v_k_3489_){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = l_Lean_Json_getObjValD(v_j_3488_, v_k_3489_);
v___x_3491_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0_spec__0(v___x_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0___boxed(lean_object* v_j_3492_, lean_object* v_k_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_j_3492_, v_k_3493_);
lean_dec_ref(v_k_3493_);
return v_res_3494_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = 1;
v___x_3502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__2));
v___x_3503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3502_, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3505_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__3);
v___x_3506_ = lean_string_append(v___x_3505_, v___x_3504_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = 1;
v___x_3510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__5));
v___x_3511_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__6);
v___x_3513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__4);
v___x_3514_ = lean_string_append(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3516_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__7);
v___x_3517_ = lean_string_append(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson(lean_object* v_json_3518_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3520_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson_spec__0(v_json_3518_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3530_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3530_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3530_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3525_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__8);
v___x_3526_ = lean_string_append(v___x_3525_, v_a_3521_);
lean_dec(v_a_3521_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3526_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3520_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3520_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 0);
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v_a_3539_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3520_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3520_);
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
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(size_t v_sz_3549_, size_t v_i_3550_, lean_object* v_bs_3551_){
_start:
{
uint8_t v___x_3552_; 
v___x_3552_ = lean_usize_dec_lt(v_i_3550_, v_sz_3549_);
if (v___x_3552_ == 0)
{
return v_bs_3551_;
}
else
{
lean_object* v_v_3553_; lean_object* v___x_3554_; lean_object* v_bs_x27_3555_; lean_object* v___x_3556_; size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
v_v_3553_ = lean_array_uget(v_bs_3551_, v_i_3550_);
v___x_3554_ = lean_unsigned_to_nat(0u);
v_bs_x27_3555_ = lean_array_uset(v_bs_3551_, v_i_3550_, v___x_3554_);
v___x_3556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_v_3553_);
v___x_3557_ = ((size_t)1ULL);
v___x_3558_ = lean_usize_add(v_i_3550_, v___x_3557_);
v___x_3559_ = lean_array_uset(v_bs_x27_3555_, v_i_3550_, v___x_3556_);
v_i_3550_ = v___x_3558_;
v_bs_3551_ = v___x_3559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3561_, lean_object* v_i_3562_, lean_object* v_bs_3563_){
_start:
{
size_t v_sz_boxed_3564_; size_t v_i_boxed_3565_; lean_object* v_res_3566_; 
v_sz_boxed_3564_ = lean_unbox_usize(v_sz_3561_);
lean_dec(v_sz_3561_);
v_i_boxed_3565_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_res_3566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_boxed_3564_, v_i_boxed_3565_, v_bs_3563_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(lean_object* v_a_3567_){
_start:
{
size_t v_sz_3568_; size_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_sz_3568_ = lean_array_size(v_a_3567_);
v___x_3569_ = ((size_t)0ULL);
v___x_3570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0_spec__0(v_sz_3568_, v___x_3569_, v_a_3567_);
v___x_3571_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportClosureParams_toJson(lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3573_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportClosureParams_fromJson___closed__0));
v___x_3574_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanImportClosureParams_toJson_spec__0(v_x_3572_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_box(0);
v___x_3577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___x_3576_);
v___x_3579_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3580_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3578_, v___x_3579_);
v___x_3581_ = l_Lean_Json_mkObj(v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(lean_object* v_j_3584_, lean_object* v_k_3585_){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = l_Lean_Json_getObjValD(v_j_3584_, v_k_3585_);
v___x_3587_ = l_Lean_Json_getStr_x3f(v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0___boxed(lean_object* v_j_3588_, lean_object* v_k_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_j_3588_, v_k_3589_);
lean_dec_ref(v_k_3589_);
return v_res_3590_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = 1;
v___x_3598_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__2));
v___x_3599_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_3601_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__3);
v___x_3602_ = lean_string_append(v___x_3601_, v___x_3600_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3605_ = 1;
v___x_3606_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__5));
v___x_3607_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3606_, v___x_3605_);
return v___x_3607_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__6);
v___x_3609_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__4);
v___x_3610_ = lean_string_append(v___x_3609_, v___x_3608_);
return v___x_3610_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_3612_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__7);
v___x_3613_ = lean_string_append(v___x_3612_, v___x_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson(lean_object* v_json_3614_){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3616_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_3614_, v___x_3615_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3626_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3626_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3626_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3621_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__8);
v___x_3622_ = lean_string_append(v___x_3621_, v_a_3617_);
lean_dec(v_a_3617_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 0, v___x_3622_);
v___x_3624_ = v___x_3619_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
else
{
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
v_a_3627_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3616_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3616_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set_tag(v___x_3629_, 0);
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3616_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3616_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanStaleDependencyParams_toJson(lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3646_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson___closed__0));
v___x_3647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3647_, 0, v_x_3645_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_box(0);
v___x_3650_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
lean_ctor_set(v___x_3651_, 1, v___x_3649_);
v___x_3652_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_3653_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_3651_, v___x_3652_);
v___x_3654_ = l_Lean_Json_mkObj(v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx(lean_object* v_x_3657_){
_start:
{
if (lean_obj_tag(v_x_3657_) == 0)
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_unsigned_to_nat(0u);
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_unsigned_to_nat(1u);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorIdx___boxed(lean_object* v_x_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Lsp_OpenNamespace_ctorIdx(v_x_3660_);
lean_dec_ref(v_x_3660_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___redArg(lean_object* v_t_3662_, lean_object* v_k_3663_){
_start:
{
if (lean_obj_tag(v_t_3662_) == 0)
{
lean_object* v_namespace_3664_; lean_object* v_exceptions_3665_; lean_object* v___x_3666_; 
v_namespace_3664_ = lean_ctor_get(v_t_3662_, 0);
lean_inc(v_namespace_3664_);
v_exceptions_3665_ = lean_ctor_get(v_t_3662_, 1);
lean_inc_ref(v_exceptions_3665_);
lean_dec_ref(v_t_3662_);
v___x_3666_ = lean_apply_2(v_k_3663_, v_namespace_3664_, v_exceptions_3665_);
return v___x_3666_;
}
else
{
lean_object* v_from_3667_; lean_object* v_to_3668_; lean_object* v___x_3669_; 
v_from_3667_ = lean_ctor_get(v_t_3662_, 0);
lean_inc(v_from_3667_);
v_to_3668_ = lean_ctor_get(v_t_3662_, 1);
lean_inc(v_to_3668_);
lean_dec_ref(v_t_3662_);
v___x_3669_ = lean_apply_2(v_k_3663_, v_from_3667_, v_to_3668_);
return v___x_3669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim(lean_object* v_motive_3670_, lean_object* v_ctorIdx_3671_, lean_object* v_t_3672_, lean_object* v_h_3673_, lean_object* v_k_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3672_, v_k_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_ctorElim___boxed(lean_object* v_motive_3676_, lean_object* v_ctorIdx_3677_, lean_object* v_t_3678_, lean_object* v_h_3679_, lean_object* v_k_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Lsp_OpenNamespace_ctorElim(v_motive_3676_, v_ctorIdx_3677_, v_t_3678_, v_h_3679_, v_k_3680_);
lean_dec(v_ctorIdx_3677_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim___redArg(lean_object* v_t_3682_, lean_object* v_allExcept_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3682_, v_allExcept_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_allExcept_elim(lean_object* v_motive_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_, lean_object* v_allExcept_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3686_, v_allExcept_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim___redArg(lean_object* v_t_3690_, lean_object* v_renamed_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3690_, v_renamed_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_OpenNamespace_renamed_elim(lean_object* v_motive_3693_, lean_object* v_t_3694_, lean_object* v_h_3695_, lean_object* v_renamed_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Lsp_OpenNamespace_ctorElim___redArg(v_t_3694_, v_renamed_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_bs_3700_){
_start:
{
uint8_t v___x_3701_; 
v___x_3701_ = lean_usize_dec_lt(v_i_3699_, v_sz_3698_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_bs_3700_);
return v___x_3702_;
}
else
{
lean_object* v_v_3703_; lean_object* v___x_3704_; 
v_v_3703_ = lean_array_uget_borrowed(v_bs_3700_, v_i_3699_);
lean_inc(v_v_3703_);
v___x_3704_ = l_Lean_Name_fromJson_x3f(v_v_3703_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v_bs_3700_);
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3704_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3704_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v_bs_x27_3715_; size_t v___x_3716_; size_t v___x_3717_; lean_object* v___x_3718_; 
v_a_3713_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3704_);
v___x_3714_ = lean_unsigned_to_nat(0u);
v_bs_x27_3715_ = lean_array_uset(v_bs_3700_, v_i_3699_, v___x_3714_);
v___x_3716_ = ((size_t)1ULL);
v___x_3717_ = lean_usize_add(v_i_3699_, v___x_3716_);
v___x_3718_ = lean_array_uset(v_bs_x27_3715_, v_i_3699_, v_a_3713_);
v_i_3699_ = v___x_3717_;
v_bs_3700_ = v___x_3718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0___boxed(lean_object* v_sz_3720_, lean_object* v_i_3721_, lean_object* v_bs_3722_){
_start:
{
size_t v_sz_boxed_3723_; size_t v_i_boxed_3724_; lean_object* v_res_3725_; 
v_sz_boxed_3723_ = lean_unbox_usize(v_sz_3720_);
lean_dec(v_sz_3720_);
v_i_boxed_3724_ = lean_unbox_usize(v_i_3721_);
lean_dec(v_i_3721_);
v_res_3725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_boxed_3723_, v_i_boxed_3724_, v_bs_3722_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(lean_object* v_x_3726_){
_start:
{
if (lean_obj_tag(v_x_3726_) == 4)
{
lean_object* v_elems_3727_; size_t v_sz_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v_elems_3727_ = lean_ctor_get(v_x_3726_, 0);
lean_inc_ref(v_elems_3727_);
lean_dec_ref(v_x_3726_);
v_sz_3728_ = lean_array_size(v_elems_3727_);
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0_spec__0(v_sz_3728_, v___x_3729_, v_elems_3727_);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3731_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3732_ = lean_unsigned_to_nat(80u);
v___x_3733_ = l_Lean_Json_pretty(v_x_3726_, v___x_3732_);
v___x_3734_ = lean_string_append(v___x_3731_, v___x_3733_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3736_ = lean_string_append(v___x_3734_, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
return v___x_3737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(lean_object* v_json_3772_){
_start:
{
lean_object* v___x_3773_; 
lean_inc(v_json_3772_);
v___x_3773_ = l_Lean_Json_getTag_x3f(v_json_3772_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v___x_3774_; 
lean_dec(v_json_3772_);
v___x_3774_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__0));
return v___x_3774_;
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_val_3775_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_val_3775_);
lean_dec_ref(v___x_3773_);
v___x_3776_ = lean_box(0);
v___x_3777_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3778_ = lean_string_dec_eq(v_val_3775_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3780_ = lean_string_dec_eq(v_val_3775_, v___x_3779_);
lean_dec(v_val_3775_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec(v_json_3772_);
v___x_3781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__3));
return v___x_3781_;
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(2u);
v___x_3783_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__9));
v___x_3784_ = l_Lean_Json_parseCtorFields(v_json_3772_, v___x_3779_, v___x_3782_, v___x_3783_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3793_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3784_);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_array_get_borrowed(v___x_3776_, v_a_3793_, v___x_3794_);
lean_inc(v___x_3795_);
v___x_3796_ = l_Lean_Name_fromJson_x3f(v___x_3795_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3793_);
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_a_3805_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v___x_3796_);
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_array_get(v___x_3776_, v_a_3793_, v___x_3806_);
lean_dec(v_a_3793_);
v___x_3808_ = l_Array_fromJson_x3f___at___00Lean_Lsp_instFromJsonOpenNamespace_fromJson_spec__0(v___x_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3805_);
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3825_; 
v_a_3817_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3819_ = v___x_3808_;
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3808_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3805_);
lean_ctor_set(v___x_3821_, 1, v_a_3817_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3821_);
v___x_3823_ = v___x_3819_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec(v_val_3775_);
v___x_3826_ = lean_unsigned_to_nat(2u);
v___x_3827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__15));
v___x_3828_ = l_Lean_Json_parseCtorFields(v_json_3772_, v___x_3777_, v___x_3826_, v___x_3827_);
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
lean_dec_ref(v___x_3828_);
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_array_get_borrowed(v___x_3776_, v_a_3837_, v___x_3838_);
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
lean_dec_ref(v___x_3840_);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_array_get(v___x_3776_, v_a_3837_, v___x_3850_);
lean_dec(v_a_3837_);
v___x_3852_ = l_Lean_Name_fromJson_x3f(v___x_3851_);
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
v___x_3865_ = lean_alloc_ctor(1, 2, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(size_t v_sz_3872_, size_t v_i_3873_, lean_object* v_bs_3874_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_usize_dec_lt(v_i_3873_, v_sz_3872_);
if (v___x_3875_ == 0)
{
return v_bs_3874_;
}
else
{
lean_object* v_v_3876_; lean_object* v___x_3877_; lean_object* v_bs_x27_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; size_t v___x_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v_v_3876_ = lean_array_uget(v_bs_3874_, v_i_3873_);
v___x_3877_ = lean_unsigned_to_nat(0u);
v_bs_x27_3878_ = lean_array_uset(v_bs_3874_, v_i_3873_, v___x_3877_);
v___x_3879_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_3876_, v___x_3875_);
v___x_3880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = ((size_t)1ULL);
v___x_3882_ = lean_usize_add(v_i_3873_, v___x_3881_);
v___x_3883_ = lean_array_uset(v_bs_x27_3878_, v_i_3873_, v___x_3880_);
v_i_3873_ = v___x_3882_;
v_bs_3874_ = v___x_3883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3885_, lean_object* v_i_3886_, lean_object* v_bs_3887_){
_start:
{
size_t v_sz_boxed_3888_; size_t v_i_boxed_3889_; lean_object* v_res_3890_; 
v_sz_boxed_3888_ = lean_unbox_usize(v_sz_3885_);
lean_dec(v_sz_3885_);
v_i_boxed_3889_ = lean_unbox_usize(v_i_3886_);
lean_dec(v_i_3886_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_boxed_3888_, v_i_boxed_3889_, v_bs_3887_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(lean_object* v_a_3891_){
_start:
{
size_t v_sz_3892_; size_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_sz_3892_ = lean_array_size(v_a_3891_);
v___x_3893_ = ((size_t)0ULL);
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0_spec__0(v_sz_3892_, v___x_3893_, v_a_3891_);
v___x_3895_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonOpenNamespace_toJson(lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 0)
{
lean_object* v_namespace_3897_; lean_object* v_exceptions_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3920_; 
v_namespace_3897_ = lean_ctor_get(v_x_3896_, 0);
v_exceptions_3898_ = lean_ctor_get(v_x_3896_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_x_3896_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3900_ = v_x_3896_;
v_isShared_3901_ = v_isSharedCheck_3920_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_exceptions_3898_);
lean_inc(v_namespace_3897_);
lean_dec(v_x_3896_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3920_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3902_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__2));
v___x_3903_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__4));
v___x_3904_ = 1;
v___x_3905_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_namespace_3897_, v___x_3904_);
v___x_3906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 1, v___x_3906_);
lean_ctor_set(v___x_3900_, 0, v___x_3903_);
v___x_3908_ = v___x_3900_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3909_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__6));
v___x_3910_ = l_Array_toJson___at___00Lean_Lsp_instToJsonOpenNamespace_toJson_spec__0(v_exceptions_3898_);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3908_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = l_Lean_Json_mkObj(v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3902_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
lean_ctor_set(v___x_3917_, 1, v___x_3912_);
v___x_3918_ = l_Lean_Json_mkObj(v___x_3917_);
return v___x_3918_;
}
}
}
else
{
lean_object* v_from_3921_; lean_object* v_to_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3945_; 
v_from_3921_ = lean_ctor_get(v_x_3896_, 0);
v_to_3922_ = lean_ctor_get(v_x_3896_, 1);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_x_3896_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3924_ = v_x_3896_;
v_isShared_3925_ = v_isSharedCheck_3945_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_to_3922_);
lean_inc(v_from_3921_);
lean_dec(v_x_3896_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3945_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3926_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__1));
v___x_3927_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__10));
v___x_3928_ = 1;
v___x_3929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_from_3921_, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set_tag(v___x_3924_, 0);
lean_ctor_set(v___x_3924_, 1, v___x_3930_);
lean_ctor_set(v___x_3924_, 0, v___x_3927_);
v___x_3932_ = v___x_3924_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3933_ = ((lean_object*)(l_Lean_Lsp_instFromJsonOpenNamespace_fromJson___closed__12));
v___x_3934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_to_3922_, v___x_3928_);
v___x_3935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3933_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_box(0);
v___x_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3932_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_Json_mkObj(v___x_3939_);
v___x_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3926_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
lean_ctor_set(v___x_3942_, 1, v___x_3937_);
v___x_3943_ = l_Lean_Json_mkObj(v___x_3942_);
return v___x_3943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(size_t v_sz_3948_, size_t v_i_3949_, lean_object* v_bs_3950_){
_start:
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_usize_dec_lt(v_i_3949_, v_sz_3948_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v_bs_3950_);
return v___x_3952_;
}
else
{
lean_object* v_v_3953_; lean_object* v___x_3954_; 
v_v_3953_ = lean_array_uget_borrowed(v_bs_3950_, v_i_3949_);
lean_inc(v_v_3953_);
v___x_3954_ = l_Lean_Lsp_instFromJsonOpenNamespace_fromJson(v_v_3953_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_bs_3950_);
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3964_; lean_object* v_bs_x27_3965_; size_t v___x_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v_a_3963_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3963_);
lean_dec_ref(v___x_3954_);
v___x_3964_ = lean_unsigned_to_nat(0u);
v_bs_x27_3965_ = lean_array_uset(v_bs_3950_, v_i_3949_, v___x_3964_);
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_add(v_i_3949_, v___x_3966_);
v___x_3968_ = lean_array_uset(v_bs_x27_3965_, v_i_3949_, v_a_3963_);
v_i_3949_ = v___x_3967_;
v_bs_3950_ = v___x_3968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3970_, lean_object* v_i_3971_, lean_object* v_bs_3972_){
_start:
{
size_t v_sz_boxed_3973_; size_t v_i_boxed_3974_; lean_object* v_res_3975_; 
v_sz_boxed_3973_ = lean_unbox_usize(v_sz_3970_);
lean_dec(v_sz_3970_);
v_i_boxed_3974_ = lean_unbox_usize(v_i_3971_);
lean_dec(v_i_3971_);
v_res_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_3973_, v_i_boxed_3974_, v_bs_3972_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(lean_object* v_x_3976_){
_start:
{
if (lean_obj_tag(v_x_3976_) == 4)
{
lean_object* v_elems_3977_; size_t v_sz_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v_elems_3977_ = lean_ctor_get(v_x_3976_, 0);
lean_inc_ref(v_elems_3977_);
lean_dec_ref(v_x_3976_);
v_sz_3978_ = lean_array_size(v_elems_3977_);
v___x_3979_ = ((size_t)0ULL);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0_spec__1(v_sz_3978_, v___x_3979_, v_elems_3977_);
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3981_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_3982_ = lean_unsigned_to_nat(80u);
v___x_3983_ = l_Lean_Json_pretty(v_x_3976_, v___x_3982_);
v___x_3984_ = lean_string_append(v___x_3981_, v___x_3983_);
lean_dec_ref(v___x_3983_);
v___x_3985_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(lean_object* v_j_3988_, lean_object* v_k_3989_){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = l_Lean_Json_getObjValD(v_j_3988_, v_k_3989_);
v___x_3991_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0_spec__0(v___x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0___boxed(lean_object* v_j_3992_, lean_object* v_k_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_j_3992_, v_k_3993_);
lean_dec_ref(v_k_3993_);
return v_res_3994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = 1;
v___x_4002_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__2));
v___x_4003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4002_, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__3);
v___x_4006_ = lean_string_append(v___x_4005_, v___x_4004_);
return v___x_4006_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = 1;
v___x_4010_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__5));
v___x_4011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4010_, v___x_4009_);
return v___x_4011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__6);
v___x_4013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4014_ = lean_string_append(v___x_4013_, v___x_4012_);
return v___x_4014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4016_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__7);
v___x_4017_ = lean_string_append(v___x_4016_, v___x_4015_);
return v___x_4017_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = 1;
v___x_4022_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__10));
v___x_4023_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4022_, v___x_4021_);
return v___x_4023_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__11);
v___x_4025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__4);
v___x_4026_ = lean_string_append(v___x_4025_, v___x_4024_);
return v___x_4026_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4028_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__12);
v___x_4029_ = lean_string_append(v___x_4028_, v___x_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(lean_object* v_json_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
lean_inc(v_json_4030_);
v___x_4032_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4030_, v___x_4031_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4042_; 
lean_dec(v_json_4030_);
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4042_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4042_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4037_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__8);
v___x_4038_ = lean_string_append(v___x_4037_, v_a_4033_);
lean_dec(v_a_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4038_);
v___x_4040_ = v___x_4035_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_json_4030_);
v_a_4043_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4032_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4032_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set_tag(v___x_4045_, 0);
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_a_4051_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4032_);
v___x_4052_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4053_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModuleQuery_fromJson_spec__0(v_json_4030_, v___x_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_a_4051_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4058_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__13);
v___x_4059_ = lean_string_append(v___x_4058_, v_a_4054_);
lean_dec(v_a_4054_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v___x_4059_);
v___x_4061_ = v___x_4056_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
else
{
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_a_4051_);
v_a_4064_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4053_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4053_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set_tag(v___x_4066_, 0);
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4080_; 
v_a_4072_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4074_ = v___x_4053_;
v_isShared_4075_ = v_isSharedCheck_4080_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4053_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4080_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_a_4051_);
lean_ctor_set(v___x_4076_, 1, v_a_4072_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4076_);
v___x_4078_ = v___x_4074_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(size_t v_sz_4083_, size_t v_i_4084_, lean_object* v_bs_4085_){
_start:
{
uint8_t v___x_4086_; 
v___x_4086_ = lean_usize_dec_lt(v_i_4084_, v_sz_4083_);
if (v___x_4086_ == 0)
{
return v_bs_4085_;
}
else
{
lean_object* v_v_4087_; lean_object* v___x_4088_; lean_object* v_bs_x27_4089_; lean_object* v___x_4090_; size_t v___x_4091_; size_t v___x_4092_; lean_object* v___x_4093_; 
v_v_4087_ = lean_array_uget(v_bs_4085_, v_i_4084_);
v___x_4088_ = lean_unsigned_to_nat(0u);
v_bs_x27_4089_ = lean_array_uset(v_bs_4085_, v_i_4084_, v___x_4088_);
v___x_4090_ = l_Lean_Lsp_instToJsonOpenNamespace_toJson(v_v_4087_);
v___x_4091_ = ((size_t)1ULL);
v___x_4092_ = lean_usize_add(v_i_4084_, v___x_4091_);
v___x_4093_ = lean_array_uset(v_bs_x27_4089_, v_i_4084_, v___x_4090_);
v_i_4084_ = v___x_4092_;
v_bs_4085_ = v___x_4093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4095_, lean_object* v_i_4096_, lean_object* v_bs_4097_){
_start:
{
size_t v_sz_boxed_4098_; size_t v_i_boxed_4099_; lean_object* v_res_4100_; 
v_sz_boxed_4098_ = lean_unbox_usize(v_sz_4095_);
lean_dec(v_sz_4095_);
v_i_boxed_4099_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_boxed_4098_, v_i_boxed_4099_, v_bs_4097_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(lean_object* v_a_4101_){
_start:
{
size_t v_sz_4102_; size_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_sz_4102_ = lean_array_size(v_a_4101_);
v___x_4103_ = ((size_t)0ULL);
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0_spec__0(v_sz_4102_, v___x_4103_, v_a_4101_);
v___x_4105_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(lean_object* v_x_4106_){
_start:
{
lean_object* v_identifier_4107_; lean_object* v_openNamespaces_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4128_; 
v_identifier_4107_ = lean_ctor_get(v_x_4106_, 0);
v_openNamespaces_4108_ = lean_ctor_get(v_x_4106_, 1);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_x_4106_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4110_ = v_x_4106_;
v_isShared_4111_ = v_isSharedCheck_4128_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_openNamespaces_4108_);
lean_inc(v_identifier_4107_);
lean_dec(v_x_4106_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4128_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__0));
v___x_4113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_identifier_4107_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 1, v___x_4113_);
lean_ctor_set(v___x_4110_, 0, v___x_4112_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4116_ = lean_box(0);
v___x_4117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson___closed__9));
v___x_4119_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanModuleQuery_toJson_spec__0(v_openNamespaces_4108_);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v___x_4116_);
v___x_4122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v___x_4116_);
v___x_4123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4117_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4125_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4123_, v___x_4124_);
v___x_4126_ = l_Lean_Json_mkObj(v___x_4125_);
return v___x_4126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(lean_object* v_j_4134_, lean_object* v_k_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Json_getObjValD(v_j_4134_, v_k_4135_);
switch(lean_obj_tag(v___x_4136_))
{
case 3:
{
lean_object* v_s_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4145_; 
v_s_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_s_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 0);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_s_4137_);
v___x_4142_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
}
}
case 2:
{
lean_object* v_n_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4154_; 
v_n_4146_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4148_ = v___x_4136_;
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_n_4146_);
lean_dec(v___x_4136_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4154_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set_tag(v___x_4148_, 1);
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_n_4146_);
v___x_4151_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
}
default: 
{
lean_object* v___x_4155_; 
lean_dec(v___x_4136_);
v___x_4155_ = ((lean_object*)(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___closed__1));
return v___x_4155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0___boxed(lean_object* v_j_4156_, lean_object* v_k_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_j_4156_, v_k_4157_);
lean_dec_ref(v_k_4157_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_4159_, size_t v_i_4160_, lean_object* v_bs_4161_){
_start:
{
uint8_t v___x_4162_; 
v___x_4162_ = lean_usize_dec_lt(v_i_4160_, v_sz_4159_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_bs_4161_);
return v___x_4163_;
}
else
{
lean_object* v_v_4164_; lean_object* v___x_4165_; 
v_v_4164_ = lean_array_uget_borrowed(v_bs_4161_, v_i_4160_);
lean_inc(v_v_4164_);
v___x_4165_ = l_Lean_Lsp_instFromJsonLeanModuleQuery_fromJson(v_v_4164_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v_bs_4161_);
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4175_; lean_object* v_bs_x27_4176_; size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v_a_4174_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4165_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v_bs_x27_4176_ = lean_array_uset(v_bs_4161_, v_i_4160_, v___x_4175_);
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4160_, v___x_4177_);
v___x_4179_ = lean_array_uset(v_bs_x27_4176_, v_i_4160_, v_a_4174_);
v_i_4160_ = v___x_4178_;
v_bs_4161_ = v___x_4179_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4181_, lean_object* v_i_4182_, lean_object* v_bs_4183_){
_start:
{
size_t v_sz_boxed_4184_; size_t v_i_boxed_4185_; lean_object* v_res_4186_; 
v_sz_boxed_4184_ = lean_unbox_usize(v_sz_4181_);
lean_dec(v_sz_4181_);
v_i_boxed_4185_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4184_, v_i_boxed_4185_, v_bs_4183_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(lean_object* v_x_4187_){
_start:
{
if (lean_obj_tag(v_x_4187_) == 4)
{
lean_object* v_elems_4188_; size_t v_sz_4189_; size_t v___x_4190_; lean_object* v___x_4191_; 
v_elems_4188_ = lean_ctor_get(v_x_4187_, 0);
lean_inc_ref(v_elems_4188_);
lean_dec_ref(v_x_4187_);
v_sz_4189_ = lean_array_size(v_elems_4188_);
v___x_4190_ = ((size_t)0ULL);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1_spec__2(v_sz_4189_, v___x_4190_, v_elems_4188_);
return v___x_4191_;
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4192_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4193_ = lean_unsigned_to_nat(80u);
v___x_4194_ = l_Lean_Json_pretty(v_x_4187_, v___x_4193_);
v___x_4195_ = lean_string_append(v___x_4192_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4196_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4197_ = lean_string_append(v___x_4195_, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
return v___x_4198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(lean_object* v_j_4199_, lean_object* v_k_4200_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = l_Lean_Json_getObjValD(v_j_4199_, v_k_4200_);
v___x_4202_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1_spec__1(v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1___boxed(lean_object* v_j_4203_, lean_object* v_k_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_j_4203_, v_k_4204_);
lean_dec_ref(v_k_4204_);
return v_res_4205_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = 1;
v___x_4213_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__2));
v___x_4214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__3);
v___x_4217_ = lean_string_append(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = 1;
v___x_4221_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__5));
v___x_4222_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4221_, v___x_4220_);
return v___x_4222_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__6);
v___x_4224_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4225_ = lean_string_append(v___x_4224_, v___x_4223_);
return v___x_4225_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4227_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__7);
v___x_4228_ = lean_string_append(v___x_4227_, v___x_4226_);
return v___x_4228_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = 1;
v___x_4233_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__10));
v___x_4234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4233_, v___x_4232_);
return v___x_4234_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__11);
v___x_4236_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__4);
v___x_4237_ = lean_string_append(v___x_4236_, v___x_4235_);
return v___x_4237_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4238_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4239_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__12);
v___x_4240_ = lean_string_append(v___x_4239_, v___x_4238_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson(lean_object* v_json_4241_){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
lean_inc(v_json_4241_);
v___x_4243_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__0(v_json_4241_, v___x_4242_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4253_; 
lean_dec(v_json_4241_);
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4253_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4253_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4248_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__8);
v___x_4249_ = lean_string_append(v___x_4248_, v_a_4244_);
lean_dec(v_a_4244_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4249_);
v___x_4251_ = v___x_4246_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
else
{
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec(v_json_4241_);
v_a_4254_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4243_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4243_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
lean_ctor_set_tag(v___x_4256_, 0);
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_a_4262_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4243_);
v___x_4263_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4264_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson_spec__1(v_json_4241_, v___x_4263_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v_a_4262_);
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4267_ = v___x_4264_;
v_isShared_4268_ = v_isSharedCheck_4274_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4274_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4269_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__13);
v___x_4270_ = lean_string_append(v___x_4269_, v_a_4265_);
lean_dec(v_a_4265_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 0, v___x_4270_);
v___x_4272_ = v___x_4267_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
else
{
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_a_4262_);
v_a_4275_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4264_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4264_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set_tag(v___x_4277_, 0);
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
v_a_4283_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4285_ = v___x_4264_;
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4264_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v_a_4262_);
lean_ctor_set(v___x_4287_, 1, v_a_4283_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v___x_4287_);
v___x_4289_ = v___x_4285_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(size_t v_sz_4294_, size_t v_i_4295_, lean_object* v_bs_4296_){
_start:
{
uint8_t v___x_4297_; 
v___x_4297_ = lean_usize_dec_lt(v_i_4295_, v_sz_4294_);
if (v___x_4297_ == 0)
{
return v_bs_4296_;
}
else
{
lean_object* v_v_4298_; lean_object* v___x_4299_; lean_object* v_bs_x27_4300_; lean_object* v___x_4301_; size_t v___x_4302_; size_t v___x_4303_; lean_object* v___x_4304_; 
v_v_4298_ = lean_array_uget(v_bs_4296_, v_i_4295_);
v___x_4299_ = lean_unsigned_to_nat(0u);
v_bs_x27_4300_ = lean_array_uset(v_bs_4296_, v_i_4295_, v___x_4299_);
v___x_4301_ = l_Lean_Lsp_instToJsonLeanModuleQuery_toJson(v_v_4298_);
v___x_4302_ = ((size_t)1ULL);
v___x_4303_ = lean_usize_add(v_i_4295_, v___x_4302_);
v___x_4304_ = lean_array_uset(v_bs_x27_4300_, v_i_4295_, v___x_4301_);
v_i_4295_ = v___x_4303_;
v_bs_4296_ = v___x_4304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4306_, lean_object* v_i_4307_, lean_object* v_bs_4308_){
_start:
{
size_t v_sz_boxed_4309_; size_t v_i_boxed_4310_; lean_object* v_res_4311_; 
v_sz_boxed_4309_ = lean_unbox_usize(v_sz_4306_);
lean_dec(v_sz_4306_);
v_i_boxed_4310_ = lean_unbox_usize(v_i_4307_);
lean_dec(v_i_4307_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_boxed_4309_, v_i_boxed_4310_, v_bs_4308_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(lean_object* v_a_4312_){
_start:
{
size_t v_sz_4313_; size_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_sz_4313_ = lean_array_size(v_a_4312_);
v___x_4314_ = ((size_t)0ULL);
v___x_4315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0_spec__0(v_sz_4313_, v___x_4314_, v_a_4312_);
v___x_4316_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object* v_x_4317_){
_start:
{
lean_object* v_sourceRequestID_4318_; lean_object* v_queries_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4357_; 
v_sourceRequestID_4318_ = lean_ctor_get(v_x_4317_, 0);
v_queries_4319_ = lean_ctor_get(v_x_4317_, 1);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_x_4317_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4321_ = v_x_4317_;
v_isShared_4322_ = v_isSharedCheck_4357_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_queries_4319_);
lean_inc(v_sourceRequestID_4318_);
lean_dec(v_x_4317_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4357_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___y_4325_; 
v___x_4323_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__0));
switch(lean_obj_tag(v_sourceRequestID_4318_))
{
case 0:
{
lean_object* v_s_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
v_s_4340_ = lean_ctor_get(v_sourceRequestID_4318_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_sourceRequestID_4318_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v_sourceRequestID_4318_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_s_4340_);
lean_dec(v_sourceRequestID_4318_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set_tag(v___x_4342_, 3);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_s_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
v___y_4325_ = v___x_4345_;
goto v___jp_4324_;
}
}
}
case 1:
{
lean_object* v_n_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_n_4348_ = lean_ctor_get(v_sourceRequestID_4318_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_sourceRequestID_4318_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v_sourceRequestID_4318_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_n_4348_);
lean_dec(v_sourceRequestID_4318_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
lean_ctor_set_tag(v___x_4350_, 2);
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_n_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
v___y_4325_ = v___x_4353_;
goto v___jp_4324_;
}
}
}
default: 
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_box(0);
v___y_4325_ = v___x_4356_;
goto v___jp_4324_;
}
}
v___jp_4324_:
{
lean_object* v___x_4327_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 1, v___y_4325_);
lean_ctor_set(v___x_4321_, 0, v___x_4323_);
v___x_4327_ = v___x_4321_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v___y_4325_);
v___x_4327_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4328_ = lean_box(0);
v___x_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleParams_fromJson___closed__9));
v___x_4331_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleParams_toJson_spec__0(v_queries_4319_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
v___x_4333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set(v___x_4333_, 1, v___x_4328_);
v___x_4334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4328_);
v___x_4335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4329_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
v___x_4336_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4337_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4335_, v___x_4336_);
v___x_4338_ = l_Lean_Json_mkObj(v___x_4337_);
return v___x_4338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(lean_object* v_j_4360_, lean_object* v_k_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = l_Lean_Json_getObjValD(v_j_4360_, v_k_4361_);
v___x_4363_ = l_Lean_Name_fromJson_x3f(v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0___boxed(lean_object* v_j_4364_, lean_object* v_k_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_j_4364_, v_k_4365_);
lean_dec_ref(v_k_4365_);
return v_res_4366_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = 1;
v___x_4374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__2));
v___x_4375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4374_, v___x_4373_);
return v___x_4375_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4377_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__3);
v___x_4378_ = lean_string_append(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4381_ = 1;
v___x_4382_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__5));
v___x_4383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4382_, v___x_4381_);
return v___x_4383_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4385_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4386_ = lean_string_append(v___x_4385_, v___x_4384_);
return v___x_4386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4388_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__7);
v___x_4389_ = lean_string_append(v___x_4388_, v___x_4387_);
return v___x_4389_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11(void){
_start:
{
uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4393_ = 1;
v___x_4394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__10));
v___x_4395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4394_, v___x_4393_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4396_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4398_ = lean_string_append(v___x_4397_, v___x_4396_);
return v___x_4398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__12);
v___x_4401_ = lean_string_append(v___x_4400_, v___x_4399_);
return v___x_4401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16(void){
_start:
{
uint8_t v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4405_ = 1;
v___x_4406_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__15));
v___x_4407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4406_, v___x_4405_);
return v___x_4407_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4408_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__16);
v___x_4409_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__4);
v___x_4410_ = lean_string_append(v___x_4409_, v___x_4408_);
return v___x_4410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__17);
v___x_4413_ = lean_string_append(v___x_4412_, v___x_4411_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(lean_object* v_json_4414_){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4414_);
v___x_4416_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4414_, v___x_4415_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4426_; 
lean_dec(v_json_4414_);
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4419_ = v___x_4416_;
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4416_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v___x_4421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__8);
v___x_4422_ = lean_string_append(v___x_4421_, v_a_4417_);
lean_dec(v_a_4417_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4422_);
v___x_4424_ = v___x_4419_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
else
{
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_json_4414_);
v_a_4427_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4416_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4416_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
lean_ctor_set_tag(v___x_4429_, 0);
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4435_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4435_);
lean_dec_ref(v___x_4416_);
v___x_4436_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
lean_inc(v_json_4414_);
v___x_4437_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4414_, v___x_4436_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v_a_4435_);
lean_dec(v_json_4414_);
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4440_ = v___x_4437_;
v_isShared_4441_ = v_isSharedCheck_4447_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4447_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4442_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__13);
v___x_4443_ = lean_string_append(v___x_4442_, v_a_4438_);
lean_dec(v_a_4438_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___x_4443_);
v___x_4445_ = v___x_4440_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
else
{
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_a_4435_);
lean_dec(v_json_4414_);
v_a_4448_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4437_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4437_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set_tag(v___x_4450_, 0);
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_a_4456_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4456_);
lean_dec_ref(v___x_4437_);
v___x_4457_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4458_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4414_, v___x_4457_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_a_4456_);
lean_dec(v_a_4435_);
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4468_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4468_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__18);
v___x_4464_ = lean_string_append(v___x_4463_, v_a_4459_);
lean_dec(v_a_4459_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4464_);
v___x_4466_ = v___x_4461_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
else
{
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_a_4456_);
lean_dec(v_a_4435_);
v_a_4469_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4458_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4458_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set_tag(v___x_4471_, 0);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4486_; 
v_a_4477_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4479_ = v___x_4458_;
v_isShared_4480_ = v_isSharedCheck_4486_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4458_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4486_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; uint8_t v___x_4482_; lean_object* v___x_4484_; 
v___x_4481_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4481_, 0, v_a_4435_);
lean_ctor_set(v___x_4481_, 1, v_a_4456_);
v___x_4482_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
lean_ctor_set_uint8(v___x_4481_, sizeof(void*)*2, v___x_4482_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4481_);
v___x_4484_ = v___x_4479_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4481_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanIdentifier_toJson(lean_object* v_x_4489_){
_start:
{
lean_object* v_module_4490_; lean_object* v_decl_4491_; uint8_t v_isExactMatch_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_module_4490_ = lean_ctor_get(v_x_4489_, 0);
lean_inc(v_module_4490_);
v_decl_4491_ = lean_ctor_get(v_x_4489_, 1);
lean_inc(v_decl_4491_);
v_isExactMatch_4492_ = lean_ctor_get_uint8(v_x_4489_, sizeof(void*)*2);
lean_dec_ref(v_x_4489_);
v___x_4493_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4494_ = 1;
v___x_4495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4490_, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
v___x_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4493_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = lean_box(0);
v___x_4499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4497_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
v___x_4500_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4491_, v___x_4494_);
v___x_4502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4500_);
lean_ctor_set(v___x_4503_, 1, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
lean_ctor_set(v___x_4504_, 1, v___x_4498_);
v___x_4505_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__14));
v___x_4506_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4506_, 0, v_isExactMatch_4492_);
v___x_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4505_);
lean_ctor_set(v___x_4507_, 1, v___x_4506_);
v___x_4508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
lean_ctor_set(v___x_4508_, 1, v___x_4498_);
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
lean_ctor_set(v___x_4509_, 1, v___x_4498_);
v___x_4510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4504_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4499_);
lean_ctor_set(v___x_4511_, 1, v___x_4510_);
v___x_4512_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4513_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4511_, v___x_4512_);
v___x_4514_ = l_Lean_Json_mkObj(v___x_4513_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4517_, size_t v_i_4518_, lean_object* v_bs_4519_){
_start:
{
uint8_t v___x_4520_; 
v___x_4520_ = lean_usize_dec_lt(v_i_4518_, v_sz_4517_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
v___x_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4521_, 0, v_bs_4519_);
return v___x_4521_;
}
else
{
lean_object* v_v_4522_; lean_object* v___x_4523_; 
v_v_4522_ = lean_array_uget_borrowed(v_bs_4519_, v_i_4518_);
lean_inc(v_v_4522_);
v___x_4523_ = l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson(v_v_4522_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec_ref(v_bs_4519_);
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4523_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4533_; lean_object* v_bs_x27_4534_; size_t v___x_4535_; size_t v___x_4536_; lean_object* v___x_4537_; 
v_a_4532_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4532_);
lean_dec_ref(v___x_4523_);
v___x_4533_ = lean_unsigned_to_nat(0u);
v_bs_x27_4534_ = lean_array_uset(v_bs_4519_, v_i_4518_, v___x_4533_);
v___x_4535_ = ((size_t)1ULL);
v___x_4536_ = lean_usize_add(v_i_4518_, v___x_4535_);
v___x_4537_ = lean_array_uset(v_bs_x27_4534_, v_i_4518_, v_a_4532_);
v_i_4518_ = v___x_4536_;
v_bs_4519_ = v___x_4537_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4539_, lean_object* v_i_4540_, lean_object* v_bs_4541_){
_start:
{
size_t v_sz_boxed_4542_; size_t v_i_boxed_4543_; lean_object* v_res_4544_; 
v_sz_boxed_4542_ = lean_unbox_usize(v_sz_4539_);
lean_dec(v_sz_4539_);
v_i_boxed_4543_ = lean_unbox_usize(v_i_4540_);
lean_dec(v_i_4540_);
v_res_4544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4542_, v_i_boxed_4543_, v_bs_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4545_){
_start:
{
if (lean_obj_tag(v_x_4545_) == 4)
{
lean_object* v_elems_4546_; size_t v_sz_4547_; size_t v___x_4548_; lean_object* v___x_4549_; 
v_elems_4546_ = lean_ctor_get(v_x_4545_, 0);
lean_inc_ref(v_elems_4546_);
lean_dec_ref(v_x_4545_);
v_sz_4547_ = lean_array_size(v_elems_4546_);
v___x_4548_ = ((size_t)0ULL);
v___x_4549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4547_, v___x_4548_, v_elems_4546_);
return v___x_4549_;
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4550_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4551_ = lean_unsigned_to_nat(80u);
v___x_4552_ = l_Lean_Json_pretty(v_x_4545_, v___x_4551_);
v___x_4553_ = lean_string_append(v___x_4550_, v___x_4552_);
lean_dec_ref(v___x_4552_);
v___x_4554_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4555_ = lean_string_append(v___x_4553_, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
return v___x_4556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(size_t v_sz_4557_, size_t v_i_4558_, lean_object* v_bs_4559_){
_start:
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_usize_dec_lt(v_i_4558_, v_sz_4557_);
if (v___x_4560_ == 0)
{
lean_object* v___x_4561_; 
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v_bs_4559_);
return v___x_4561_;
}
else
{
lean_object* v_v_4562_; lean_object* v___x_4563_; 
v_v_4562_ = lean_array_uget_borrowed(v_bs_4559_, v_i_4558_);
lean_inc(v_v_4562_);
v___x_4563_ = l_Array_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__1(v_v_4562_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec_ref(v_bs_4559_);
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4563_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4573_; lean_object* v_bs_x27_4574_; size_t v___x_4575_; size_t v___x_4576_; lean_object* v___x_4577_; 
v_a_4572_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4572_);
lean_dec_ref(v___x_4563_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v_bs_x27_4574_ = lean_array_uset(v_bs_4559_, v_i_4558_, v___x_4573_);
v___x_4575_ = ((size_t)1ULL);
v___x_4576_ = lean_usize_add(v_i_4558_, v___x_4575_);
v___x_4577_ = lean_array_uset(v_bs_x27_4574_, v_i_4558_, v_a_4572_);
v_i_4558_ = v___x_4576_;
v_bs_4559_ = v___x_4577_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_4579_, lean_object* v_i_4580_, lean_object* v_bs_4581_){
_start:
{
size_t v_sz_boxed_4582_; size_t v_i_boxed_4583_; lean_object* v_res_4584_; 
v_sz_boxed_4582_ = lean_unbox_usize(v_sz_4579_);
lean_dec(v_sz_4579_);
v_i_boxed_4583_ = lean_unbox_usize(v_i_4580_);
lean_dec(v_i_4580_);
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_4582_, v_i_boxed_4583_, v_bs_4581_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(lean_object* v_x_4585_){
_start:
{
if (lean_obj_tag(v_x_4585_) == 4)
{
lean_object* v_elems_4586_; size_t v_sz_4587_; size_t v___x_4588_; lean_object* v___x_4589_; 
v_elems_4586_ = lean_ctor_get(v_x_4585_, 0);
lean_inc_ref(v_elems_4586_);
lean_dec_ref(v_x_4585_);
v_sz_4587_ = lean_array_size(v_elems_4586_);
v___x_4588_ = ((size_t)0ULL);
v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0_spec__2(v_sz_4587_, v___x_4588_, v_elems_4586_);
return v___x_4589_;
}
else
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4590_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__0));
v___x_4591_ = lean_unsigned_to_nat(80u);
v___x_4592_ = l_Lean_Json_pretty(v_x_4585_, v___x_4591_);
v___x_4593_ = lean_string_append(v___x_4590_, v___x_4592_);
lean_dec_ref(v___x_4592_);
v___x_4594_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__2_spec__2___closed__1));
v___x_4595_ = lean_string_append(v___x_4593_, v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(lean_object* v_j_4597_, lean_object* v_k_4598_){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = l_Lean_Json_getObjValD(v_j_4597_, v_k_4598_);
v___x_4600_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0_spec__0(v___x_4599_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0___boxed(lean_object* v_j_4601_, lean_object* v_k_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_j_4601_, v_k_4602_);
lean_dec_ref(v_k_4602_);
return v_res_4603_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = 1;
v___x_4611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__2));
v___x_4612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4611_, v___x_4610_);
return v___x_4612_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4614_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__3);
v___x_4615_ = lean_string_append(v___x_4614_, v___x_4613_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = 1;
v___x_4619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__5));
v___x_4620_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4619_, v___x_4618_);
return v___x_4620_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4621_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__6);
v___x_4622_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__4);
v___x_4623_ = lean_string_append(v___x_4622_, v___x_4621_);
return v___x_4623_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4625_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__7);
v___x_4626_ = lean_string_append(v___x_4625_, v___x_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object* v_json_4627_){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4629_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson_spec__0(v_json_4627_, v___x_4628_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4639_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4632_ = v___x_4629_;
v_isShared_4633_ = v_isSharedCheck_4639_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4629_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4639_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v___x_4634_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__8);
v___x_4635_ = lean_string_append(v___x_4634_, v_a_4630_);
lean_dec(v_a_4630_);
if (v_isShared_4633_ == 0)
{
lean_ctor_set(v___x_4632_, 0, v___x_4635_);
v___x_4637_ = v___x_4632_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
else
{
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
v_a_4640_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4629_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4629_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
lean_ctor_set_tag(v___x_4642_, 0);
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
else
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
v_a_4648_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4629_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4629_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(size_t v_sz_4658_, size_t v_i_4659_, lean_object* v_bs_4660_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_usize_dec_lt(v_i_4659_, v_sz_4658_);
if (v___x_4661_ == 0)
{
return v_bs_4660_;
}
else
{
lean_object* v_v_4662_; lean_object* v___x_4663_; lean_object* v_bs_x27_4664_; lean_object* v___x_4665_; size_t v___x_4666_; size_t v___x_4667_; lean_object* v___x_4668_; 
v_v_4662_ = lean_array_uget(v_bs_4660_, v_i_4659_);
v___x_4663_ = lean_unsigned_to_nat(0u);
v_bs_x27_4664_ = lean_array_uset(v_bs_4660_, v_i_4659_, v___x_4663_);
v___x_4665_ = l_Lean_Lsp_instToJsonLeanIdentifier_toJson(v_v_4662_);
v___x_4666_ = ((size_t)1ULL);
v___x_4667_ = lean_usize_add(v_i_4659_, v___x_4666_);
v___x_4668_ = lean_array_uset(v_bs_x27_4664_, v_i_4659_, v___x_4665_);
v_i_4659_ = v___x_4667_;
v_bs_4660_ = v___x_4668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4670_, lean_object* v_i_4671_, lean_object* v_bs_4672_){
_start:
{
size_t v_sz_boxed_4673_; size_t v_i_boxed_4674_; lean_object* v_res_4675_; 
v_sz_boxed_4673_ = lean_unbox_usize(v_sz_4670_);
lean_dec(v_sz_4670_);
v_i_boxed_4674_ = lean_unbox_usize(v_i_4671_);
lean_dec(v_i_4671_);
v_res_4675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4673_, v_i_boxed_4674_, v_bs_4672_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(lean_object* v_a_4676_){
_start:
{
size_t v_sz_4677_; size_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v_sz_4677_ = lean_array_size(v_a_4676_);
v___x_4678_ = ((size_t)0ULL);
v___x_4679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0_spec__1(v_sz_4677_, v___x_4678_, v_a_4676_);
v___x_4680_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(size_t v_sz_4681_, size_t v_i_4682_, lean_object* v_bs_4683_){
_start:
{
uint8_t v___x_4684_; 
v___x_4684_ = lean_usize_dec_lt(v_i_4682_, v_sz_4681_);
if (v___x_4684_ == 0)
{
return v_bs_4683_;
}
else
{
lean_object* v_v_4685_; lean_object* v___x_4686_; lean_object* v_bs_x27_4687_; lean_object* v___x_4688_; size_t v___x_4689_; size_t v___x_4690_; lean_object* v___x_4691_; 
v_v_4685_ = lean_array_uget(v_bs_4683_, v_i_4682_);
v___x_4686_ = lean_unsigned_to_nat(0u);
v_bs_x27_4687_ = lean_array_uset(v_bs_4683_, v_i_4682_, v___x_4686_);
v___x_4688_ = l_Array_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__0(v_v_4685_);
v___x_4689_ = ((size_t)1ULL);
v___x_4690_ = lean_usize_add(v_i_4682_, v___x_4689_);
v___x_4691_ = lean_array_uset(v_bs_x27_4687_, v_i_4682_, v___x_4688_);
v_i_4682_ = v___x_4690_;
v_bs_4683_ = v___x_4691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1___boxed(lean_object* v_sz_4693_, lean_object* v_i_4694_, lean_object* v_bs_4695_){
_start:
{
size_t v_sz_boxed_4696_; size_t v_i_boxed_4697_; lean_object* v_res_4698_; 
v_sz_boxed_4696_ = lean_unbox_usize(v_sz_4693_);
lean_dec(v_sz_4693_);
v_i_boxed_4697_ = lean_unbox_usize(v_i_4694_);
lean_dec(v_i_4694_);
v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_boxed_4696_, v_i_boxed_4697_, v_bs_4695_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(lean_object* v_a_4699_){
_start:
{
size_t v_sz_4700_; size_t v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v_sz_4700_ = lean_array_size(v_a_4699_);
v___x_4701_ = ((size_t)0ULL);
v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0_spec__1(v_sz_4700_, v___x_4701_, v_a_4699_);
v___x_4703_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson(lean_object* v_x_4704_){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4705_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson___closed__0));
v___x_4706_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanQueryModuleResponse_toJson_spec__0(v_x_4704_);
v___x_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4705_);
lean_ctor_set(v___x_4707_, 1, v___x_4706_);
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4707_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
v___x_4710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
lean_ctor_set(v___x_4710_, 1, v___x_4708_);
v___x_4711_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4712_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4710_, v___x_4711_);
v___x_4713_ = l_Lean_Json_mkObj(v___x_4712_);
return v___x_4713_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4725_ = 1;
v___x_4726_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__1));
v___x_4727_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4726_, v___x_4725_);
return v___x_4727_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4729_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__2);
v___x_4730_ = lean_string_append(v___x_4729_, v___x_4728_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4731_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__6);
v___x_4732_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4733_ = lean_string_append(v___x_4732_, v___x_4731_);
return v___x_4733_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4734_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4735_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__4);
v___x_4736_ = lean_string_append(v___x_4735_, v___x_4734_);
return v___x_4736_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__11);
v___x_4738_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__3);
v___x_4739_ = lean_string_append(v___x_4738_, v___x_4737_);
return v___x_4739_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4741_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__6);
v___x_4742_ = lean_string_append(v___x_4741_, v___x_4740_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(lean_object* v_json_4743_){
_start:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
lean_inc(v_json_4743_);
v___x_4745_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4743_, v___x_4744_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v_json_4743_);
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
v___x_4750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__5);
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
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_json_4743_);
v_a_4756_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4745_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4745_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set_tag(v___x_4758_, 0);
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v_a_4764_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4764_);
lean_dec_ref(v___x_4745_);
v___x_4765_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4766_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanIdentifier_fromJson_spec__0(v_json_4743_, v___x_4765_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4776_; 
lean_dec(v_a_4764_);
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4776_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4776_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4771_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson___closed__7);
v___x_4772_ = lean_string_append(v___x_4771_, v_a_4767_);
lean_dec(v_a_4767_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4772_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
else
{
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
lean_dec(v_a_4764_);
v_a_4777_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4766_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4766_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
lean_ctor_set_tag(v___x_4779_, 0);
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4793_; 
v_a_4785_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4787_ = v___x_4766_;
v_isShared_4788_ = v_isSharedCheck_4793_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4766_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4793_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v_a_4764_);
lean_ctor_set(v___x_4789_, 1, v_a_4785_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4789_);
v___x_4791_ = v___x_4787_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(lean_object* v_x_4796_){
_start:
{
lean_object* v_module_4797_; lean_object* v_decl_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4821_; 
v_module_4797_ = lean_ctor_get(v_x_4796_, 0);
v_decl_4798_ = lean_ctor_get(v_x_4796_, 1);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_x_4796_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4800_ = v_x_4796_;
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_decl_4798_);
lean_inc(v_module_4797_);
lean_dec(v_x_4796_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4821_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4802_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__0));
v___x_4803_ = 1;
v___x_4804_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_4797_, v___x_4803_);
v___x_4805_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 1, v___x_4805_);
lean_ctor_set(v___x_4800_, 0, v___x_4802_);
v___x_4807_ = v___x_4800_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4808_ = lean_box(0);
v___x_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4807_);
lean_ctor_set(v___x_4809_, 1, v___x_4808_);
v___x_4810_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanIdentifier_fromJson___closed__9));
v___x_4811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_4798_, v___x_4803_);
v___x_4812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4810_);
lean_ctor_set(v___x_4813_, 1, v___x_4812_);
v___x_4814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
lean_ctor_set(v___x_4814_, 1, v___x_4808_);
v___x_4815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
lean_ctor_set(v___x_4815_, 1, v___x_4808_);
v___x_4816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4809_);
lean_ctor_set(v___x_4816_, 1, v___x_4815_);
v___x_4817_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_4818_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_4816_, v___x_4817_);
v___x_4819_ = l_Lean_Json_mkObj(v___x_4818_);
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(lean_object* v_j_4824_, lean_object* v_k_4825_){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = l_Lean_Json_getObjValD(v_j_4824_, v_k_4825_);
v___x_4827_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1___boxed(lean_object* v_j_4828_, lean_object* v_k_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_j_4828_, v_k_4829_);
lean_dec_ref(v_k_4829_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(lean_object* v_x_4833_){
_start:
{
if (lean_obj_tag(v_x_4833_) == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3___closed__0));
return v___x_4834_;
}
else
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Lean_Lsp_instFromJsonLeanDeclIdent_fromJson(v_x_4833_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4835_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4835_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4839_ == 0)
{
v___x_4841_ = v___x_4838_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4852_; 
v_a_4844_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4846_ = v___x_4835_;
v_isShared_4847_ = v_isSharedCheck_4852_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4835_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4852_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
v___x_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4848_, 0, v_a_4844_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v___x_4848_);
v___x_4850_ = v___x_4846_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(lean_object* v_j_4853_, lean_object* v_k_4854_){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = l_Lean_Json_getObjValD(v_j_4853_, v_k_4854_);
v___x_4856_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2_spec__3(v___x_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2___boxed(lean_object* v_j_4857_, lean_object* v_k_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_j_4857_, v_k_4858_);
lean_dec_ref(v_k_4858_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_4862_){
_start:
{
if (lean_obj_tag(v_x_4862_) == 0)
{
lean_object* v___x_4863_; 
v___x_4863_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_4863_;
}
else
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_4862_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4881_; 
v_a_4873_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4875_ = v___x_4864_;
v_isShared_4876_ = v_isSharedCheck_4881_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4864_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4881_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4877_, 0, v_a_4873_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 0, v___x_4877_);
v___x_4879_ = v___x_4875_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(lean_object* v_j_4882_, lean_object* v_k_4883_){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = l_Lean_Json_getObjValD(v_j_4882_, v_k_4883_);
v___x_4885_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0_spec__0(v___x_4884_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0___boxed(lean_object* v_j_4886_, lean_object* v_k_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_j_4886_, v_k_4887_);
lean_dec_ref(v_k_4887_);
return v_res_4888_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4895_ = 1;
v___x_4896_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__2));
v___x_4897_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4896_, v___x_4895_);
return v___x_4897_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4898_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__6));
v___x_4899_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__3);
v___x_4900_ = lean_string_append(v___x_4899_, v___x_4898_);
return v___x_4900_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7(void){
_start:
{
uint8_t v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = 1;
v___x_4905_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__6));
v___x_4906_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4905_, v___x_4904_);
return v___x_4906_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4907_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__7);
v___x_4908_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4909_ = lean_string_append(v___x_4908_, v___x_4907_);
return v___x_4909_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4911_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__8);
v___x_4912_ = lean_string_append(v___x_4911_, v___x_4910_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12(void){
_start:
{
uint8_t v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = 1;
v___x_4917_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__11));
v___x_4918_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4917_, v___x_4916_);
return v___x_4918_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4919_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__12);
v___x_4920_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4921_ = lean_string_append(v___x_4920_, v___x_4919_);
return v___x_4921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14(void){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4922_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__13);
v___x_4924_ = lean_string_append(v___x_4923_, v___x_4922_);
return v___x_4924_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17(void){
_start:
{
uint8_t v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4928_ = 1;
v___x_4929_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__16));
v___x_4930_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4929_, v___x_4928_);
return v___x_4930_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18(void){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__17);
v___x_4932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4933_ = lean_string_append(v___x_4932_, v___x_4931_);
return v___x_4933_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4934_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4935_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__18);
v___x_4936_ = lean_string_append(v___x_4935_, v___x_4934_);
return v___x_4936_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22(void){
_start:
{
uint8_t v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4940_ = 1;
v___x_4941_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__21));
v___x_4942_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4941_, v___x_4940_);
return v___x_4942_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23(void){
_start:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__22);
v___x_4944_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4945_ = lean_string_append(v___x_4944_, v___x_4943_);
return v___x_4945_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4947_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__23);
v___x_4948_ = lean_string_append(v___x_4947_, v___x_4946_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28(void){
_start:
{
uint8_t v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4953_ = 1;
v___x_4954_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__27));
v___x_4955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4954_, v___x_4953_);
return v___x_4955_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4956_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__28);
v___x_4957_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4958_ = lean_string_append(v___x_4957_, v___x_4956_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__29);
v___x_4961_ = lean_string_append(v___x_4960_, v___x_4959_);
return v___x_4961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33(void){
_start:
{
uint8_t v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4965_ = 1;
v___x_4966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__32));
v___x_4967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4966_, v___x_4965_);
return v___x_4967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__33);
v___x_4969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__4);
v___x_4970_ = lean_string_append(v___x_4969_, v___x_4968_);
return v___x_4970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson___closed__11));
v___x_4972_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__34);
v___x_4973_ = lean_string_append(v___x_4972_, v___x_4971_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson(lean_object* v_json_4974_){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
lean_inc(v_json_4974_);
v___x_4976_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__0(v_json_4974_, v___x_4975_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4986_; 
lean_dec(v_json_4974_);
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4979_ = v___x_4976_;
v_isShared_4980_ = v_isSharedCheck_4986_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4976_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4986_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__9);
v___x_4982_ = lean_string_append(v___x_4981_, v_a_4977_);
lean_dec(v_a_4977_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set(v___x_4979_, 0, v___x_4982_);
v___x_4984_ = v___x_4979_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
else
{
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec(v_json_4974_);
v_a_4987_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4976_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4976_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set_tag(v___x_4989_, 0);
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v_a_4995_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4995_);
lean_dec_ref(v___x_4976_);
v___x_4996_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
lean_inc(v_json_4974_);
v___x_4997_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanStaleDependencyParams_fromJson_spec__0(v_json_4974_, v___x_4996_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5007_; 
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5000_ = v___x_4997_;
v_isShared_5001_ = v_isSharedCheck_5007_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4997_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5007_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5005_; 
v___x_5002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__14);
v___x_5003_ = lean_string_append(v___x_5002_, v_a_4998_);
lean_dec(v_a_4998_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 0, v___x_5003_);
v___x_5005_ = v___x_5000_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
else
{
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5008_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4997_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4997_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
lean_ctor_set_tag(v___x_5010_, 0);
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v_a_5016_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_a_5016_);
lean_dec_ref(v___x_4997_);
v___x_5017_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
lean_inc(v_json_4974_);
v___x_5018_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4974_, v___x_5017_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5028_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5028_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5023_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__19);
v___x_5024_ = lean_string_append(v___x_5023_, v_a_5019_);
lean_dec(v_a_5019_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5024_);
v___x_5026_ = v___x_5021_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
else
{
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5029_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5018_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5018_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
lean_ctor_set_tag(v___x_5031_, 0);
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v_a_5037_ = lean_ctor_get(v___x_5018_, 0);
lean_inc(v_a_5037_);
lean_dec_ref(v___x_5018_);
v___x_5038_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
lean_inc(v_json_4974_);
v___x_5039_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__1(v_json_4974_, v___x_5038_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5049_; 
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5049_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5049_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5044_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__24);
v___x_5045_ = lean_string_append(v___x_5044_, v_a_5040_);
lean_dec(v_a_5040_);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5045_);
v___x_5047_ = v___x_5042_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
else
{
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5050_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5039_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5039_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set_tag(v___x_5052_, 0);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_a_5058_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_a_5058_);
lean_dec_ref(v___x_5039_);
v___x_5059_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
lean_inc(v_json_4974_);
v___x_5060_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanLocationLink_fromJson_spec__2(v_json_4974_, v___x_5059_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5070_; 
lean_dec(v_a_5058_);
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5070_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5070_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5068_; 
v___x_5065_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__30);
v___x_5066_ = lean_string_append(v___x_5065_, v_a_5061_);
lean_dec(v_a_5061_);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v___x_5066_);
v___x_5068_ = v___x_5063_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
else
{
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec(v_a_5058_);
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
lean_dec(v_json_4974_);
v_a_5071_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5060_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5060_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set_tag(v___x_5073_, 0);
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
else
{
lean_object* v_a_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v_a_5079_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5079_);
lean_dec_ref(v___x_5060_);
v___x_5080_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5081_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanILeanHeaderSetupInfoParams_fromJson_spec__1(v_json_4974_, v___x_5080_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5091_; 
lean_dec(v_a_5079_);
lean_dec(v_a_5058_);
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5084_ = v___x_5081_;
v_isShared_5085_ = v_isSharedCheck_5091_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5081_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5091_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5089_; 
v___x_5086_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35, &l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__35);
v___x_5087_ = lean_string_append(v___x_5086_, v_a_5082_);
lean_dec(v_a_5082_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 0, v___x_5087_);
v___x_5089_ = v___x_5084_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
else
{
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_dec(v_a_5079_);
lean_dec(v_a_5058_);
lean_dec(v_a_5037_);
lean_dec(v_a_5016_);
lean_dec(v_a_4995_);
v_a_5092_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_5081_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5081_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
lean_ctor_set_tag(v___x_5094_, 0);
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5110_; 
v_a_5100_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5102_ = v___x_5081_;
v_isShared_5103_ = v_isSharedCheck_5110_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5081_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5110_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; lean_object* v___x_5108_; 
v___x_5104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5104_, 0, v_a_4995_);
lean_ctor_set(v___x_5104_, 1, v_a_5016_);
lean_ctor_set(v___x_5104_, 2, v_a_5037_);
lean_ctor_set(v___x_5104_, 3, v_a_5058_);
v___x_5105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
lean_ctor_set(v___x_5105_, 1, v_a_5079_);
v___x_5106_ = lean_unbox(v_a_5100_);
lean_dec(v_a_5100_);
lean_ctor_set_uint8(v___x_5105_, sizeof(void*)*2, v___x_5106_);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v___x_5105_);
v___x_5108_ = v___x_5102_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5105_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(lean_object* v_k_5113_, lean_object* v_x_5114_){
_start:
{
if (lean_obj_tag(v_x_5114_) == 0)
{
lean_object* v___x_5115_; 
lean_dec_ref(v_k_5113_);
v___x_5115_ = lean_box(0);
return v___x_5115_;
}
else
{
lean_object* v_val_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v_val_5116_ = lean_ctor_get(v_x_5114_, 0);
lean_inc(v_val_5116_);
lean_dec_ref(v_x_5114_);
v___x_5117_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_5116_);
v___x_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5118_, 0, v_k_5113_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = lean_box(0);
v___x_5120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5118_);
lean_ctor_set(v___x_5120_, 1, v___x_5119_);
return v___x_5120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(lean_object* v_k_5121_, lean_object* v_x_5122_){
_start:
{
if (lean_obj_tag(v_x_5122_) == 0)
{
lean_object* v___x_5123_; 
lean_dec_ref(v_k_5121_);
v___x_5123_ = lean_box(0);
return v___x_5123_;
}
else
{
lean_object* v_val_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_val_5124_ = lean_ctor_get(v_x_5122_, 0);
lean_inc(v_val_5124_);
lean_dec_ref(v_x_5122_);
v___x_5125_ = l_Lean_Lsp_instToJsonLeanDeclIdent_toJson(v_val_5124_);
v___x_5126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5126_, 0, v_k_5121_);
lean_ctor_set(v___x_5126_, 1, v___x_5125_);
v___x_5127_ = lean_box(0);
v___x_5128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5126_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
return v___x_5128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanLocationLink_toJson(lean_object* v_x_5129_){
_start:
{
lean_object* v_toLocationLink_5130_; lean_object* v_ident_x3f_5131_; uint8_t v_isDefault_5132_; lean_object* v_originSelectionRange_x3f_5133_; lean_object* v_targetUri_5134_; lean_object* v_targetRange_5135_; lean_object* v_targetSelectionRange_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v_toLocationLink_5130_ = lean_ctor_get(v_x_5129_, 0);
lean_inc_ref(v_toLocationLink_5130_);
v_ident_x3f_5131_ = lean_ctor_get(v_x_5129_, 1);
lean_inc(v_ident_x3f_5131_);
v_isDefault_5132_ = lean_ctor_get_uint8(v_x_5129_, sizeof(void*)*2);
lean_dec_ref(v_x_5129_);
v_originSelectionRange_x3f_5133_ = lean_ctor_get(v_toLocationLink_5130_, 0);
lean_inc(v_originSelectionRange_x3f_5133_);
v_targetUri_5134_ = lean_ctor_get(v_toLocationLink_5130_, 1);
lean_inc_ref(v_targetUri_5134_);
v_targetRange_5135_ = lean_ctor_get(v_toLocationLink_5130_, 2);
lean_inc_ref(v_targetRange_5135_);
v_targetSelectionRange_5136_ = lean_ctor_get(v_toLocationLink_5130_, 3);
lean_inc_ref(v_targetSelectionRange_5136_);
lean_dec_ref(v_toLocationLink_5130_);
v___x_5137_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__0));
v___x_5138_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__0(v___x_5137_, v_originSelectionRange_x3f_5133_);
v___x_5139_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__10));
v___x_5140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5140_, 0, v_targetUri_5134_);
v___x_5141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = lean_box(0);
v___x_5143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__15));
v___x_5145_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_5135_);
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5144_);
lean_ctor_set(v___x_5146_, 1, v___x_5145_);
v___x_5147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5146_);
lean_ctor_set(v___x_5147_, 1, v___x_5142_);
v___x_5148_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__20));
v___x_5149_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_5136_);
v___x_5150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5148_);
lean_ctor_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
lean_ctor_set(v___x_5151_, 1, v___x_5142_);
v___x_5152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__25));
v___x_5153_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanLocationLink_toJson_spec__1(v___x_5152_, v_ident_x3f_5131_);
v___x_5154_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanLocationLink_fromJson___closed__31));
v___x_5155_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5155_, 0, v_isDefault_5132_);
v___x_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5154_);
lean_ctor_set(v___x_5156_, 1, v___x_5155_);
v___x_5157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
lean_ctor_set(v___x_5157_, 1, v___x_5142_);
v___x_5158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5158_, 0, v___x_5157_);
lean_ctor_set(v___x_5158_, 1, v___x_5142_);
v___x_5159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5153_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5160_, 0, v___x_5151_);
lean_ctor_set(v___x_5160_, 1, v___x_5159_);
v___x_5161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5147_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5143_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
v___x_5163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5138_);
lean_ctor_set(v___x_5163_, 1, v___x_5162_);
v___x_5164_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson___closed__0));
v___x_5165_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanILeanHeaderSetupInfoParams_toJson_spec__1(v___x_5163_, v___x_5164_);
v___x_5166_ = l_Lean_Json_mkObj(v___x_5165_);
return v___x_5166_;
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
l_Lean_Lsp_instEmptyCollectionDecls = _init_l_Lean_Lsp_instEmptyCollectionDecls();
lean_mark_persistent(l_Lean_Lsp_instEmptyCollectionDecls);
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

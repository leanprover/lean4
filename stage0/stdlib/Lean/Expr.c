// Lean compiler output
// Module: Lean.Expr
// Imports: public import Init.Data.Hashable public import Init.System.IO public import Lean.Data.LBool public import Lean.Level import Init.Omega
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Lean_Level_hasMVar(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint8_t lean_uint64_to_uint8(uint64_t);
uint32_t lean_uint8_to_uint32(uint8_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint32_t lean_uint64_to_uint32(uint64_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint64_t lean_uint32_to_uint64(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_instReprLevel_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_instReprKVMap_repr___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_KVMap_size(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_decEq___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedLiteral_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedLiteral_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLiteral_default = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedLiteral = (const lean_object*)&l_Lean_instInhabitedLiteral_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqLiteral_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqLiteral___closed__0 = (const lean_object*)&l_Lean_instBEqLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqLiteral = (const lean_object*)&l_Lean_instBEqLiteral___closed__0_value;
static const lean_string_object l_Lean_instReprLiteral_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Literal.natVal"};
static const lean_object* l_Lean_instReprLiteral_repr___closed__0 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__1 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__2 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__2_value;
static lean_once_cell_t l_Lean_instReprLiteral_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLiteral_repr___closed__3;
static lean_once_cell_t l_Lean_instReprLiteral_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLiteral_repr___closed__4;
static const lean_string_object l_Lean_instReprLiteral_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Literal.strVal"};
static const lean_object* l_Lean_instReprLiteral_repr___closed__5 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__5_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__5_value)}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__6 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprLiteral_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprLiteral_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprLiteral_repr___closed__7 = (const lean_object*)&l_Lean_instReprLiteral_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLiteral_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLiteral___closed__0 = (const lean_object*)&l_Lean_instReprLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLiteral = (const lean_object*)&l_Lean_instReprLiteral___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Literal_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLiteral___closed__0 = (const lean_object*)&l_Lean_instHashableLiteral___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLiteral = (const lean_object*)&l_Lean_instHashableLiteral___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instLTLiteral;
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqBinderInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqBinderInfo___closed__0 = (const lean_object*)&l_Lean_instBEqBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqBinderInfo = (const lean_object*)&l_Lean_instBEqBinderInfo___closed__0_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.BinderInfo.default"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__0 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__1 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__1_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.BinderInfo.implicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__2 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__3 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__3_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.BinderInfo.strictImplicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__4 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__5 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__5_value;
static const lean_string_object l_Lean_instReprBinderInfo_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.BinderInfo.instImplicit"};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__6 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprBinderInfo_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprBinderInfo_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprBinderInfo_repr___closed__7 = (const lean_object*)&l_Lean_instReprBinderInfo_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprBinderInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprBinderInfo___closed__0 = (const lean_object*)&l_Lean_instReprBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprBinderInfo = (const lean_object*)&l_Lean_instReprBinderInfo___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_BinderInfo_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableBinderInfo___closed__0 = (const lean_object*)&l_Lean_instHashableBinderInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableBinderInfo = (const lean_object*)&l_Lean_instHashableBinderInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_empty;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1___aux__1;
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instBEqData__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqData__1___closed__0 = (const lean_object*)&l_Lean_instBEqData__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqData__1 = (const lean_object*)&l_Lean_instBEqData__1___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
uint64_t lean_expr_mk_data(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_mk_app_data(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (hasLevelMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (hasExprMVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " (hasFVar := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (approxDepth := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expr.mkData "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_instReprData__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " (looseBVarRange := "};
static const lean_object* l_Lean_instReprData__1___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprData__1___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprData__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprData__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprData__1___closed__0 = (const lean_object*)&l_Lean_instReprData__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprData__1 = (const lean_object*)&l_Lean_instReprData__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqFVarId___closed__0 = (const lean_object*)&l_Lean_instBEqFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqFVarId = (const lean_object*)&l_Lean_instBEqFVarId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableFVarId___closed__0 = (const lean_object*)&l_Lean_instHashableFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableFVarId = (const lean_object*)&l_Lean_instHashableFVarId___closed__0_value;
static const lean_closure_object l_Lean_instReprFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprFVarId___closed__0 = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprFVarId = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdSet;
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
static const lean_closure_object l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instSingletonFVarIdFVarIdSet___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instSingletonFVarIdFVarIdSet___closed__0 = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instSingletonFVarIdFVarIdSet = (const lean_object*)&l_Lean_instSingletonFVarIdFVarIdSet___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0;
static lean_once_cell_t l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdHashSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdHashSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdHashSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId;
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqMVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqMVarId___closed__0 = (const lean_object*)&l_Lean_instBEqMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqMVarId = (const lean_object*)&l_Lean_instBEqMVarId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableMVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableMVarId___closed__0 = (const lean_object*)&l_Lean_instHashableMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableMVarId = (const lean_object*)&l_Lean_instHashableMVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprMVarId = (const lean_object*)&l_Lean_instReprFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdSet;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdSet___aux__1;
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdSet;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.bvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__0 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__1 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__1_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__2 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__2_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.fvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__3 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__3_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__3_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__4 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__5 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__5_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.mvar"};
static const lean_object* l_Lean_instReprExpr_repr___closed__6 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__6_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__6_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__7 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__7_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__8 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__8_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.sort"};
static const lean_object* l_Lean_instReprExpr_repr___closed__9 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__9_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__9_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__10 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__10_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__11 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__11_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Expr.const"};
static const lean_object* l_Lean_instReprExpr_repr___closed__12 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__12_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__12_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__13 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__13_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__14 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__14_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.app"};
static const lean_object* l_Lean_instReprExpr_repr___closed__15 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__15_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__15_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__16 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__16_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__17 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__17_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.lam"};
static const lean_object* l_Lean_instReprExpr_repr___closed__18 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__18_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__18_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__19 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__19_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__20 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__20_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.forallE"};
static const lean_object* l_Lean_instReprExpr_repr___closed__21 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__21_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__21_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__22 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__22_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__23 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__23_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.letE"};
static const lean_object* l_Lean_instReprExpr_repr___closed__24 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__24_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__24_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__25 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__25_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__26 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__26_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.Expr.lit"};
static const lean_object* l_Lean_instReprExpr_repr___closed__27 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__27_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__27_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__28 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__28_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__28_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__29 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__29_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Expr.mdata"};
static const lean_object* l_Lean_instReprExpr_repr___closed__30 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__30_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__30_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__31 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__31_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__31_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__32 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__32_value;
static const lean_string_object l_Lean_instReprExpr_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Expr.proj"};
static const lean_object* l_Lean_instReprExpr_repr___closed__33 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__33_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__33_value)}};
static const lean_object* l_Lean_instReprExpr_repr___closed__34 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__34_value;
static const lean_ctor_object l_Lean_instReprExpr_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprExpr_repr___closed__34_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprExpr_repr___closed__35 = (const lean_object*)&l_Lean_instReprExpr_repr___closed__35_value;
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprExpr___closed__0 = (const lean_object*)&l_Lean_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprExpr = (const lean_object*)&l_Lean_instReprExpr___closed__0_value;
static const lean_string_object l_Lean_instInhabitedExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedExpr___closed__0 = (const lean_object*)&l_Lean_instInhabitedExpr___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedExpr___closed__1 = (const lean_object*)&l_Lean_instInhabitedExpr___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExpr;
static const lean_string_object l_Lean_Expr_ctorName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__0 = (const lean_object*)&l_Lean_Expr_ctorName___closed__0_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__1 = (const lean_object*)&l_Lean_Expr_ctorName___closed__1_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mvar"};
static const lean_object* l_Lean_Expr_ctorName___closed__2 = (const lean_object*)&l_Lean_Expr_ctorName___closed__2_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_Lean_Expr_ctorName___closed__3 = (const lean_object*)&l_Lean_Expr_ctorName___closed__3_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Expr_ctorName___closed__4 = (const lean_object*)&l_Lean_Expr_ctorName___closed__4_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Expr_ctorName___closed__5 = (const lean_object*)&l_Lean_Expr_ctorName___closed__5_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_Lean_Expr_ctorName___closed__6 = (const lean_object*)&l_Lean_Expr_ctorName___closed__6_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_Lean_Expr_ctorName___closed__7 = (const lean_object*)&l_Lean_Expr_ctorName___closed__7_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_Lean_Expr_ctorName___closed__8 = (const lean_object*)&l_Lean_Expr_ctorName___closed__8_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l_Lean_Expr_ctorName___closed__9 = (const lean_object*)&l_Lean_Expr_ctorName___closed__9_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_Lean_Expr_ctorName___closed__10 = (const lean_object*)&l_Lean_Expr_ctorName___closed__10_value;
static const lean_string_object l_Lean_Expr_ctorName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Expr_ctorName___closed__11 = (const lean_object*)&l_Lean_Expr_ctorName___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instHashable___closed__0 = (const lean_object*)&l_Lean_Expr_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instHashable = (const lean_object*)&l_Lean_Expr_instHashable___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static const lean_string_object l_Lean_Literal_type___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Literal_type___closed__0 = (const lean_object*)&l_Lean_Literal_type___closed__0_value;
static const lean_ctor_object l_Lean_Literal_type___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Literal_type___closed__1 = (const lean_object*)&l_Lean_Literal_type___closed__1_value;
static lean_once_cell_t l_Lean_Literal_type___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Literal_type___closed__2;
static const lean_string_object l_Lean_Literal_type___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Literal_type___closed__3 = (const lean_object*)&l_Lean_Literal_type___closed__3_value;
static const lean_ctor_object l_Lean_Literal_type___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Literal_type___closed__4 = (const lean_object*)&l_Lean_Literal_type___closed__4_value;
static lean_once_cell_t l_Lean_Literal_type___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Literal_type___closed__5;
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkSimpleThunkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_mkSimpleThunkType___closed__0 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value;
static const lean_ctor_object l_Lean_mkSimpleThunkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_mkSimpleThunkType___closed__1 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__1_value;
static const lean_string_object l_Lean_mkSimpleThunkType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_mkSimpleThunkType___closed__2 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__2_value;
static const lean_ctor_object l_Lean_mkSimpleThunkType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkSimpleThunkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_mkSimpleThunkType___closed__3 = (const lean_object*)&l_Lean_mkSimpleThunkType___closed__3_value;
static lean_once_cell_t l_Lean_mkSimpleThunkType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkSimpleThunkType___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
static const lean_string_object l_Lean_mkInstOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_mkInstOfNatNat___closed__0 = (const lean_object*)&l_Lean_mkInstOfNatNat___closed__0_value;
static const lean_ctor_object l_Lean_mkInstOfNatNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInstOfNatNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_mkInstOfNatNat___closed__1 = (const lean_object*)&l_Lean_mkInstOfNatNat___closed__1_value;
static lean_once_cell_t l_Lean_mkInstOfNatNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkInstOfNatNat___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object*);
static const lean_string_object l_Lean_mkNatLitCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_mkNatLitCore___closed__0 = (const lean_object*)&l_Lean_mkNatLitCore___closed__0_value;
static const lean_string_object l_Lean_mkNatLitCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_mkNatLitCore___closed__1 = (const lean_object*)&l_Lean_mkNatLitCore___closed__1_value;
static const lean_ctor_object l_Lean_mkNatLitCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatLitCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_mkNatLitCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatLitCore___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatLitCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_mkNatLitCore___closed__2 = (const lean_object*)&l_Lean_mkNatLitCore___closed__2_value;
static const lean_ctor_object l_Lean_mkNatLitCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_mkNatLitCore___closed__3 = (const lean_object*)&l_Lean_mkNatLitCore___closed__3_value;
static lean_once_cell_t l_Lean_mkNatLitCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatLitCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instBEq___closed__0 = (const lean_object*)&l_Lean_Expr_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instBEq = (const lean_object*)&l_Lean_Expr_instBEq___closed__0_value;
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv_budgeted(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_eqvBudgeted___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal_budgeted(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_equalBudgeted___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_appFn_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__0 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_appFn_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Expr.appFn!"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__1 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__1_value;
static const lean_string_object l_Lean_Expr_appFn_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l_Lean_Expr_appFn_x21___closed__2 = (const lean_object*)&l_Lean_Expr_appFn_x21___closed__2_value;
static lean_once_cell_t l_Lean_Expr_appFn_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appFn_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appArg_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.appArg!"};
static const lean_object* l_Lean_Expr_appArg_x21___closed__0 = (const lean_object*)&l_Lean_Expr_appArg_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appArg_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appArg_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appFn_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.appFn!'"};
static const lean_object* l_Lean_Expr_appFn_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_appFn_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appFn_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appFn_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_appArg_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.appArg!'"};
static const lean_object* l_Lean_Expr_appArg_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_appArg_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_appArg_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_appArg_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_sortLevel_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.sortLevel!"};
static const lean_object* l_Lean_Expr_sortLevel_x21___closed__0 = (const lean_object*)&l_Lean_Expr_sortLevel_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_sortLevel_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sort expected"};
static const lean_object* l_Lean_Expr_sortLevel_x21___closed__1 = (const lean_object*)&l_Lean_Expr_sortLevel_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_sortLevel_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_sortLevel_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_litValue_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.litValue!"};
static const lean_object* l_Lean_Expr_litValue_x21___closed__0 = (const lean_object*)&l_Lean_Expr_litValue_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_litValue_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "literal expected"};
static const lean_object* l_Lean_Expr_litValue_x21___closed__1 = (const lean_object*)&l_Lean_Expr_litValue_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_litValue_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_litValue_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isCharLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Expr_isCharLit___closed__0 = (const lean_object*)&l_Lean_Expr_isCharLit___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isCharLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isCharLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Expr_isCharLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isCharLit___closed__1_value_aux_0),((lean_object*)&l_Lean_mkNatLitCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Expr_isCharLit___closed__1 = (const lean_object*)&l_Lean_Expr_isCharLit___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_constName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.constName!"};
static const lean_object* l_Lean_Expr_constName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_constName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_constName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "constant expected"};
static const lean_object* l_Lean_Expr_constName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_constName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_constName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_constName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_constLevels_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.constLevels!"};
static const lean_object* l_Lean_Expr_constLevels_x21___closed__0 = (const lean_object*)&l_Lean_Expr_constLevels_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_constLevels_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_constLevels_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_bvarIdx_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.bvarIdx!"};
static const lean_object* l_Lean_Expr_bvarIdx_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bvarIdx_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_bvarIdx_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "bvar expected"};
static const lean_object* l_Lean_Expr_bvarIdx_x21___closed__1 = (const lean_object*)&l_Lean_Expr_bvarIdx_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_bvarIdx_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_fvarId_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.fvarId!"};
static const lean_object* l_Lean_Expr_fvarId_x21___closed__0 = (const lean_object*)&l_Lean_Expr_fvarId_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_fvarId_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fvar expected"};
static const lean_object* l_Lean_Expr_fvarId_x21___closed__1 = (const lean_object*)&l_Lean_Expr_fvarId_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_fvarId_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_fvarId_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_mvarId_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Expr.mvarId!"};
static const lean_object* l_Lean_Expr_mvarId_x21___closed__0 = (const lean_object*)&l_Lean_Expr_mvarId_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_mvarId_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mvar expected"};
static const lean_object* l_Lean_Expr_mvarId_x21___closed__1 = (const lean_object*)&l_Lean_Expr_mvarId_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_mvarId_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_mvarId_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingName!"};
static const lean_object* l_Lean_Expr_bindingName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_bindingName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "binding expected"};
static const lean_object* l_Lean_Expr_bindingName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_bindingName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_bindingName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingDomain_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.bindingDomain!"};
static const lean_object* l_Lean_Expr_bindingDomain_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingDomain_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingDomain_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingBody!"};
static const lean_object* l_Lean_Expr_bindingBody_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingBody_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingBody_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_bindingInfo_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.bindingInfo!"};
static const lean_object* l_Lean_Expr_bindingInfo_x21___closed__0 = (const lean_object*)&l_Lean_Expr_bindingInfo_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_bindingInfo_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_letName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letName!"};
static const lean_object* l_Lean_Expr_letName_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letName_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_letName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l_Lean_Expr_letName_x21___closed__1 = (const lean_object*)&l_Lean_Expr_letName_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_letName_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letType_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letType!"};
static const lean_object* l_Lean_Expr_letType_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letType_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letType_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letType_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letValue_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.letValue!"};
static const lean_object* l_Lean_Expr_letValue_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letValue_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letValue_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letValue_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.letBody!"};
static const lean_object* l_Lean_Expr_letBody_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letBody_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letBody_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_letNondep_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.letNondep!"};
static const lean_object* l_Lean_Expr_letNondep_x21___closed__0 = (const lean_object*)&l_Lean_Expr_letNondep_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_letNondep_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_letNondep_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_mdataExpr_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.mdataExpr!"};
static const lean_object* l_Lean_Expr_mdataExpr_x21___closed__0 = (const lean_object*)&l_Lean_Expr_mdataExpr_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_mdataExpr_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mdata expression expected"};
static const lean_object* l_Lean_Expr_mdataExpr_x21___closed__1 = (const lean_object*)&l_Lean_Expr_mdataExpr_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_mdataExpr_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_projExpr_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.projExpr!"};
static const lean_object* l_Lean_Expr_projExpr_x21___closed__0 = (const lean_object*)&l_Lean_Expr_projExpr_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_projExpr_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "proj expression expected"};
static const lean_object* l_Lean_Expr_projExpr_x21___closed__1 = (const lean_object*)&l_Lean_Expr_projExpr_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_projExpr_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_projExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_projIdx_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Expr.projIdx!"};
static const lean_object* l_Lean_Expr_projIdx_x21___closed__0 = (const lean_object*)&l_Lean_Expr_projIdx_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_projIdx_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_projIdx_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_getAppArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getAppArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.getAppArgsN.loop"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "too few arguments at"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_traverseApp___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkAppN___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_traverseApp___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_traverseApp___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_getRevArg_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Expr.getRevArg!"};
static const lean_object* l_Lean_Expr_getRevArg_x21___closed__0 = (const lean_object*)&l_Lean_Expr_getRevArg_x21___closed__0_value;
static const lean_string_object l_Lean_Expr_getRevArg_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid index"};
static const lean_object* l_Lean_Expr_getRevArg_x21___closed__1 = (const lean_object*)&l_Lean_Expr_getRevArg_x21___closed__1_value;
static lean_once_cell_t l_Lean_Expr_getRevArg_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_getRevArg_x21_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.getRevArg!'"};
static const lean_object* l_Lean_Expr_getRevArg_x21_x27___closed__0 = (const lean_object*)&l_Lean_Expr_getRevArg_x21_x27___closed__0_value;
static lean_once_cell_t l_Lean_Expr_getRevArg_x21_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_getRevArg_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object*, lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_dbgToString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_instToString___closed__0 = (const lean_object*)&l_Lean_Expr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Expr_instToString = (const lean_object*)&l_Lean_Expr_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
static const lean_string_object l_Lean_mkDecIsTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_mkDecIsTrue___closed__0 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__0_value;
static const lean_string_object l_Lean_mkDecIsTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_mkDecIsTrue___closed__1 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__1_value;
static const lean_ctor_object l_Lean_mkDecIsTrue___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDecIsTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_mkDecIsTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkDecIsTrue___closed__2_value_aux_0),((lean_object*)&l_Lean_mkDecIsTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l_Lean_mkDecIsTrue___closed__2 = (const lean_object*)&l_Lean_mkDecIsTrue___closed__2_value;
static lean_once_cell_t l_Lean_mkDecIsTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkDecIsTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkDecIsFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_mkDecIsFalse___closed__0 = (const lean_object*)&l_Lean_mkDecIsFalse___closed__0_value;
static const lean_ctor_object l_Lean_mkDecIsFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDecIsTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_mkDecIsFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkDecIsFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_mkDecIsFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l_Lean_mkDecIsFalse___closed__1 = (const lean_object*)&l_Lean_mkDecIsFalse___closed__1_value;
static lean_once_cell_t l_Lean_mkDecIsFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkDecIsFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq;
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instCoeExprExprStructEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeExprExprStructEq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeExprExprStructEq___closed__0 = (const lean_object*)&l_Lean_instCoeExprExprStructEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeExprExprStructEq = (const lean_object*)&l_Lean_instCoeExprExprStructEq___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_ExprStructEq_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instBEq___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instBEq = (const lean_object*)&l_Lean_ExprStructEq_instBEq___closed__0_value;
static const lean_closure_object l_Lean_ExprStructEq_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instHashable___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instHashable = (const lean_object*)&l_Lean_ExprStructEq_instHashable___closed__0_value;
static const lean_closure_object l_Lean_ExprStructEq_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_dbgToString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ExprStructEq_instToString___closed__0 = (const lean_object*)&l_Lean_ExprStructEq_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ExprStructEq_instToString = (const lean_object*)&l_Lean_ExprStructEq_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
static const lean_string_object l_Lean_Expr_getOptParamDefault_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_getOptParamDefault_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_getOptParamDefault_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "autoParam"};
static const lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Expr_getAutoParamTactic_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 161, 241, 39, 119, 172, 48, 112)}};
static const lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_getAutoParamTactic_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isOutParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "outParam"};
static const lean_object* l_Lean_Expr_isOutParam___closed__0 = (const lean_object*)&l_Lean_Expr_isOutParam___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isOutParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isOutParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 153, 87, 30, 57, 250, 25, 29)}};
static const lean_object* l_Lean_Expr_isOutParam___closed__1 = (const lean_object*)&l_Lean_Expr_isOutParam___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isSemiOutParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "semiOutParam"};
static const lean_object* l_Lean_Expr_isSemiOutParam___closed__0 = (const lean_object*)&l_Lean_Expr_isSemiOutParam___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isSemiOutParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSemiOutParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 187, 140, 108, 143, 232, 13, 120)}};
static const lean_object* l_Lean_Expr_isSemiOutParam___closed__1 = (const lean_object*)&l_Lean_Expr_isSemiOutParam___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_isFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Expr_isFalse___closed__0 = (const lean_object*)&l_Lean_Expr_isFalse___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Expr_isFalse___closed__1 = (const lean_object*)&l_Lean_Expr_isFalse___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Expr_isTrue___closed__0 = (const lean_object*)&l_Lean_Expr_isTrue___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Expr_isTrue___closed__1 = (const lean_object*)&l_Lean_Expr_isTrue___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isBoolFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__0 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value;
static const lean_string_object l_Lean_Expr_isBoolFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__1 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value;
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolFalse___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Expr_isBoolFalse___closed__2 = (const lean_object*)&l_Lean_Expr_isBoolFalse___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object*);
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value_aux_0),((lean_object*)&l_Lean_instReprData__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_isBoolTrue___closed__0 = (const lean_object*)&l_Lean_Expr_isBoolTrue___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_int_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__0 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__0_value;
static const lean_string_object l_Lean_Expr_int_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Expr_int_x3f___closed__1 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_int_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Expr_int_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_int_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_int_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Expr_int_x3f___closed__2 = (const lean_object*)&l_Lean_Expr_int_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateApp!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateFVar_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateFVar!"};
static const lean_object* l_Lean_Expr_updateFVar_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateFVar_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateFVar_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateFVar_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateConst!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateSort!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "level expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateMData!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateForall!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateForallE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallE!"};
static const lean_object* l_Lean_Expr_updateForallE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateForallE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateForallE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLambdaE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaE!"};
static const lean_object* l_Lean_Expr_updateLambdaE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateLambdaE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateLambdaE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateLet!Impl"};
static const lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLetE_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetE!"};
static const lean_object* l_Lean_Expr_updateLetE_x21___closed__0 = (const lean_object*)&l_Lean_Expr_updateLetE_x21___closed__0_value;
static lean_once_cell_t l_Lean_Expr_updateLetE_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLetE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPExplicit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__0 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value;
static const lean_string_object l_Lean_Expr_setPPExplicit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__1 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__1_value;
static const lean_ctor_object l_Lean_Expr_setPPExplicit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPExplicit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPExplicit___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 109, 223, 122, 147, 21, 229, 249)}};
static const lean_object* l_Lean_Expr_setPPExplicit___closed__2 = (const lean_object*)&l_Lean_Expr_setPPExplicit___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPUniverses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "universes"};
static const lean_object* l_Lean_Expr_setPPUniverses___closed__0 = (const lean_object*)&l_Lean_Expr_setPPUniverses___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPUniverses___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPUniverses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPUniverses___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPUniverses___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 49, 200, 238, 5, 247, 132, 121)}};
static const lean_object* l_Lean_Expr_setPPUniverses___closed__1 = (const lean_object*)&l_Lean_Expr_setPPUniverses___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPPiBinderTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "piBinderTypes"};
static const lean_object* l_Lean_Expr_setPPPiBinderTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPPiBinderTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPPiBinderTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 18, 16, 117, 190, 60, 138)}};
static const lean_object* l_Lean_Expr_setPPPiBinderTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPPiBinderTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPFunBinderTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "funBinderTypes"};
static const lean_object* l_Lean_Expr_setPPFunBinderTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPFunBinderTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPFunBinderTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 61, 49, 152, 149, 112, 61, 41)}};
static const lean_object* l_Lean_Expr_setPPFunBinderTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPFunBinderTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_setPPNumericTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "numericTypes"};
static const lean_object* l_Lean_Expr_setPPNumericTypes___closed__0 = (const lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__0_value;
static const lean_ctor_object l_Lean_Expr_setPPNumericTypes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_setPPExplicit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_Expr_setPPNumericTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 29, 124, 132, 27, 235, 94, 122)}};
static const lean_object* l_Lean_Expr_setPPNumericTypes___closed__1 = (const lean_object*)&l_Lean_Expr_setPPNumericTypes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_foldlM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_foldlM___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_foldlM___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_foldlM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object*);
static const lean_ctor_object l_Lean_mkAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_mkAnnotation___closed__0 = (const lean_object*)&l_Lean_mkAnnotation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkInaccessible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_inaccessible"};
static const lean_object* l_Lean_mkInaccessible___closed__0 = (const lean_object*)&l_Lean_mkInaccessible___closed__0_value;
static const lean_ctor_object l_Lean_mkInaccessible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInaccessible___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 29, 104, 7, 111, 207, 123, 40)}};
static const lean_object* l_Lean_mkInaccessible___closed__1 = (const lean_object*)&l_Lean_mkInaccessible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_patWithRef"};
static const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 181, 220, 147, 186, 176, 190, 234)}};
static const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey = (const lean_object*)&l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_mkLHSGoalRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_lhsGoal"};
static const lean_object* l_Lean_mkLHSGoalRaw___closed__0 = (const lean_object*)&l_Lean_mkLHSGoalRaw___closed__0_value;
static const lean_ctor_object l_Lean_mkLHSGoalRaw___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkLHSGoalRaw___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 54, 195, 36, 174, 14, 147, 139)}};
static const lean_object* l_Lean_mkLHSGoalRaw___closed__1 = (const lean_object*)&l_Lean_mkLHSGoalRaw___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object*);
static const lean_string_object l_Lean_isLHSGoal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_isLHSGoal_x3f___closed__0 = (const lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value;
static const lean_ctor_object l_Lean_isLHSGoal_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_isLHSGoal_x3f___closed__1 = (const lean_object*)&l_Lean_isLHSGoal_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_mkNot___closed__0 = (const lean_object*)&l_Lean_mkNot___closed__0_value;
static const lean_ctor_object l_Lean_mkNot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_mkNot___closed__1 = (const lean_object*)&l_Lean_mkNot___closed__1_value;
static lean_once_cell_t l_Lean_mkNot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
static const lean_string_object l_Lean_mkOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_mkOr___closed__0 = (const lean_object*)&l_Lean_mkOr___closed__0_value;
static const lean_ctor_object l_Lean_mkOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkOr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_mkOr___closed__1 = (const lean_object*)&l_Lean_mkOr___closed__1_value;
static lean_once_cell_t l_Lean_mkOr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkOr___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_mkAnd___closed__0 = (const lean_object*)&l_Lean_mkAnd___closed__0_value;
static const lean_ctor_object l_Lean_mkAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_mkAnd___closed__1 = (const lean_object*)&l_Lean_mkAnd___closed__1_value;
static lean_once_cell_t l_Lean_mkAnd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkAnd___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkAndN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkAndN___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object*);
static const lean_string_object l_Lean_mkEM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_mkEM___closed__0 = (const lean_object*)&l_Lean_mkEM___closed__0_value;
static const lean_string_object l_Lean_mkEM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "em"};
static const lean_object* l_Lean_mkEM___closed__1 = (const lean_object*)&l_Lean_mkEM___closed__1_value;
static const lean_ctor_object l_Lean_mkEM___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkEM___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_mkEM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkEM___closed__2_value_aux_0),((lean_object*)&l_Lean_mkEM___closed__1_value),LEAN_SCALAR_PTR_LITERAL(138, 250, 26, 166, 192, 110, 127, 170)}};
static const lean_object* l_Lean_mkEM___closed__2 = (const lean_object*)&l_Lean_mkEM___closed__2_value;
static lean_once_cell_t l_Lean_mkEM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkEM___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
static const lean_string_object l_Lean_mkIff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l_Lean_mkIff___closed__0 = (const lean_object*)&l_Lean_mkIff___closed__0_value;
static const lean_ctor_object l_Lean_mkIff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIff___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l_Lean_mkIff___closed__1 = (const lean_object*)&l_Lean_mkIff___closed__1_value;
static lean_once_cell_t l_Lean_mkIff___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIff___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Nat_mkType;
static const lean_string_object l_Lean_Nat_mkInstAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l_Lean_Nat_mkInstAdd___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstAdd___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l_Lean_Nat_mkInstAdd___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstAdd___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstAdd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstAdd;
static const lean_string_object l_Lean_Nat_mkInstHAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Nat_mkInstHAdd___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHAdd___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Nat_mkInstHAdd___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHAdd___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHAdd___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHAdd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHAdd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHAdd;
static const lean_string_object l_Lean_Nat_mkInstSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instSubNat"};
static const lean_object* l_Lean_Nat_mkInstSub___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstSub___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 126, 242, 252, 139, 96, 73, 92)}};
static const lean_object* l_Lean_Nat_mkInstSub___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstSub___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstSub___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstSub;
static const lean_string_object l_Lean_Nat_mkInstHSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Nat_mkInstHSub___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHSub___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Nat_mkInstHSub___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHSub___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHSub___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHSub___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHSub___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHSub;
static const lean_string_object l_Lean_Nat_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instMulNat"};
static const lean_object* l_Lean_Nat_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 250, 177, 143, 4, 122, 150, 94)}};
static const lean_object* l_Lean_Nat_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMul;
static const lean_string_object l_Lean_Nat_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Nat_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Nat_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHMul___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMul___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMul;
static const lean_string_object l_Lean_Nat_mkInstDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_Nat_mkInstDiv___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstDiv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Nat_mkInstDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Nat_mkInstDiv___closed__1_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 220, 27, 244, 214, 254, 46, 170)}};
static const lean_object* l_Lean_Nat_mkInstDiv___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstDiv___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstDiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstDiv___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstDiv;
static const lean_string_object l_Lean_Nat_mkInstHDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Nat_mkInstHDiv___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHDiv___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Nat_mkInstHDiv___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHDiv___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHDiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHDiv___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHDiv___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHDiv;
static const lean_string_object l_Lean_Nat_mkInstMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMod"};
static const lean_object* l_Lean_Nat_mkInstMod___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstMod___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Nat_mkInstMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Nat_mkInstMod___closed__1_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 28, 178, 185, 13, 18, 77, 86)}};
static const lean_object* l_Lean_Nat_mkInstMod___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstMod___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstMod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstMod___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstMod;
static const lean_string_object l_Lean_Nat_mkInstHMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMod"};
static const lean_object* l_Lean_Nat_mkInstHMod___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHMod___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 7, 29, 140, 31, 32, 204, 87)}};
static const lean_object* l_Lean_Nat_mkInstHMod___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHMod___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstHMod___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMod___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstHMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHMod___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHMod;
static const lean_string_object l_Lean_Nat_mkInstNatPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instNatPowNat"};
static const lean_object* l_Lean_Nat_mkInstNatPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstNatPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstNatPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstNatPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 252, 138, 245, 102, 141, 87, 126)}};
static const lean_object* l_Lean_Nat_mkInstNatPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstNatPow___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstNatPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstNatPow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstNatPow;
static const lean_string_object l_Lean_Nat_mkInstPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instPowNat"};
static const lean_object* l_Lean_Nat_mkInstPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 228, 103, 52, 5, 80, 7, 4)}};
static const lean_object* l_Lean_Nat_mkInstPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstPow___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstPow___closed__2;
static lean_once_cell_t l_Lean_Nat_mkInstPow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstPow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstPow;
static const lean_string_object l_Lean_Nat_mkInstHPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHPow"};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstHPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstHPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 197, 76, 235, 199, 0, 254, 199)}};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__1_value;
static const lean_ctor_object l_Lean_Nat_mkInstHPow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatLitCore___closed__3_value)}};
static const lean_object* l_Lean_Nat_mkInstHPow___closed__2 = (const lean_object*)&l_Lean_Nat_mkInstHPow___closed__2_value;
static lean_once_cell_t l_Lean_Nat_mkInstHPow___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHPow___closed__3;
static lean_once_cell_t l_Lean_Nat_mkInstHPow___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstHPow___closed__4;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstHPow;
static const lean_string_object l_Lean_Nat_mkInstLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Nat_mkInstLT___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstLT___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstLT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstLT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Nat_mkInstLT___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstLT___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstLT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstLT___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLT;
static const lean_string_object l_Lean_Nat_mkInstLE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Nat_mkInstLE___closed__0 = (const lean_object*)&l_Lean_Nat_mkInstLE___closed__0_value;
static const lean_ctor_object l_Lean_Nat_mkInstLE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Nat_mkInstLE___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Nat_mkInstLE___closed__1 = (const lean_object*)&l_Lean_Nat_mkInstLE___closed__1_value;
static lean_once_cell_t l_Lean_Nat_mkInstLE___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Nat_mkInstLE___closed__2;
LEAN_EXPORT lean_object* l_Lean_Nat_mkInstLE;
static const lean_string_object l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natAddFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__4;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__5;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__6;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__7;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natAddFn___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natAddFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natSubFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natSubFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natSubFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natMulFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natMulFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natMulFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natPowFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natPowFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natPowFn;
static const lean_string_object l_Lean_mkNatSucc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_mkNatSucc___closed__0 = (const lean_object*)&l_Lean_mkNatSucc___closed__0_value;
static const lean_ctor_object l_Lean_mkNatSucc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Literal_type___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_mkNatSucc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatSucc___closed__1_value_aux_0),((lean_object*)&l_Lean_mkNatSucc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_mkNatSucc___closed__1 = (const lean_object*)&l_Lean_mkNatSucc___closed__1_value;
static lean_once_cell_t l_Lean_mkNatSucc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatSucc___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkNatDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_mkNatDiv___closed__0 = (const lean_object*)&l_Lean_mkNatDiv___closed__0_value;
static const lean_string_object l_Lean_mkNatDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_mkNatDiv___closed__1 = (const lean_object*)&l_Lean_mkNatDiv___closed__1_value;
static const lean_ctor_object l_Lean_mkNatDiv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_mkNatDiv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatDiv___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatDiv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_mkNatDiv___closed__2 = (const lean_object*)&l_Lean_mkNatDiv___closed__2_value;
static lean_once_cell_t l_Lean_mkNatDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatDiv___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkNatDiv(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkNatMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_mkNatMod___closed__0 = (const lean_object*)&l_Lean_mkNatMod___closed__0_value;
static const lean_string_object l_Lean_mkNatMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_mkNatMod___closed__1 = (const lean_object*)&l_Lean_mkNatMod___closed__1_value;
static const lean_ctor_object l_Lean_mkNatMod___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkNatMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_mkNatMod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkNatMod___closed__2_value_aux_0),((lean_object*)&l_Lean_mkNatMod___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_mkNatMod___closed__2 = (const lean_object*)&l_Lean_mkNatMod___closed__2_value;
static lean_once_cell_t l_Lean_mkNatMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkNatMod___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkNatMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_natLEPred___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natLEPred___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natLEPred;
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__1;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__2;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_natEqPred___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_natEqPred;
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_propEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_propEq___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_propEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_propEq___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_propEq;
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_Int_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Int_mkType___closed__0 = (const lean_object*)&l_Lean_Int_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Int_mkType___closed__1 = (const lean_object*)&l_Lean_Int_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkType;
static const lean_string_object l_Lean_Int_mkInstNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Int_mkInstNeg___closed__0 = (const lean_object*)&l_Lean_Int_mkInstNeg___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstNeg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstNeg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstNeg___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstNeg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Int_mkInstNeg___closed__1 = (const lean_object*)&l_Lean_Int_mkInstNeg___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstNeg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstNeg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNeg;
static const lean_string_object l_Lean_Int_mkInstAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instAdd"};
static const lean_object* l_Lean_Int_mkInstAdd___closed__0 = (const lean_object*)&l_Lean_Int_mkInstAdd___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstAdd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstAdd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstAdd___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstAdd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 99, 69, 75, 84, 154, 200, 179)}};
static const lean_object* l_Lean_Int_mkInstAdd___closed__1 = (const lean_object*)&l_Lean_Int_mkInstAdd___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstAdd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstAdd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstAdd;
static lean_once_cell_t l_Lean_Int_mkInstHAdd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHAdd___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHAdd;
static const lean_string_object l_Lean_Int_mkInstSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instSub"};
static const lean_object* l_Lean_Int_mkInstSub___closed__0 = (const lean_object*)&l_Lean_Int_mkInstSub___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstSub___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstSub___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstSub___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstSub___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 85, 79, 77, 38, 86, 116, 189)}};
static const lean_object* l_Lean_Int_mkInstSub___closed__1 = (const lean_object*)&l_Lean_Int_mkInstSub___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstSub___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstSub___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstSub;
static lean_once_cell_t l_Lean_Int_mkInstHSub___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHSub___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHSub;
static const lean_string_object l_Lean_Int_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Int_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Int_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 121, 189, 72, 180, 169, 35, 121)}};
static const lean_object* l_Lean_Int_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Int_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMul;
static lean_once_cell_t l_Lean_Int_mkInstHMul___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHMul___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMul;
static const lean_ctor_object l_Lean_Int_mkInstDiv___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstDiv___closed__0_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 154, 103, 19, 118, 118, 20, 12)}};
static const lean_object* l_Lean_Int_mkInstDiv___closed__0 = (const lean_object*)&l_Lean_Int_mkInstDiv___closed__0_value;
static lean_once_cell_t l_Lean_Int_mkInstDiv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstDiv___closed__1;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstDiv;
static lean_once_cell_t l_Lean_Int_mkInstHDiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHDiv___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHDiv;
static const lean_ctor_object l_Lean_Int_mkInstMod___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstMod___closed__0_value_aux_0),((lean_object*)&l_Lean_Nat_mkInstMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 18, 147, 153, 76, 63, 153, 183)}};
static const lean_object* l_Lean_Int_mkInstMod___closed__0 = (const lean_object*)&l_Lean_Int_mkInstMod___closed__0_value;
static lean_once_cell_t l_Lean_Int_mkInstMod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstMod___closed__1;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstMod;
static lean_once_cell_t l_Lean_Int_mkInstHMod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHMod___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHMod;
static const lean_string_object l_Lean_Int_mkInstPow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNatPow"};
static const lean_object* l_Lean_Int_mkInstPow___closed__0 = (const lean_object*)&l_Lean_Int_mkInstPow___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstPow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstPow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstPow___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstPow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 111, 246, 9, 99, 98, 200, 100)}};
static const lean_object* l_Lean_Int_mkInstPow___closed__1 = (const lean_object*)&l_Lean_Int_mkInstPow___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstPow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstPow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPow;
static lean_once_cell_t l_Lean_Int_mkInstPowNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstPowNat___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstPowNat;
static lean_once_cell_t l_Lean_Int_mkInstHPow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstHPow___closed__0;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstHPow;
static const lean_string_object l_Lean_Int_mkInstLT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Int_mkInstLT___closed__0 = (const lean_object*)&l_Lean_Int_mkInstLT___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstLT___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstLT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstLT___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstLT___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Int_mkInstLT___closed__1 = (const lean_object*)&l_Lean_Int_mkInstLT___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstLT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstLT___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLT;
static const lean_string_object l_Lean_Int_mkInstLE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLEInt"};
static const lean_object* l_Lean_Int_mkInstLE___closed__0 = (const lean_object*)&l_Lean_Int_mkInstLE___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstLE___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Int_mkInstLE___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Int_mkInstLE___closed__1_value_aux_0),((lean_object*)&l_Lean_Int_mkInstLE___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 143, 147, 243, 104, 145, 221, 241)}};
static const lean_object* l_Lean_Int_mkInstLE___closed__1 = (const lean_object*)&l_Lean_Int_mkInstLE___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstLE___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstLE___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstLE;
static const lean_string_object l_Lean_Int_mkInstNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_Lean_Int_mkInstNatCast___closed__0 = (const lean_object*)&l_Lean_Int_mkInstNatCast___closed__0_value;
static const lean_ctor_object l_Lean_Int_mkInstNatCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkInstNatCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_Lean_Int_mkInstNatCast___closed__1 = (const lean_object*)&l_Lean_Int_mkInstNatCast___closed__1_value;
static lean_once_cell_t l_Lean_Int_mkInstNatCast___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Int_mkInstNatCast___closed__2;
LEAN_EXPORT lean_object* l_Lean_Int_mkInstNatCast;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNegFn___closed__0;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNegFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNegFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intAddFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intAddFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intSubFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intSubFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intMulFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intMulFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intDivFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intDivFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intDivFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intModFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intModFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intModFn;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intPowNatFn;
static const lean_string_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intNatCastFn;
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLEPred___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intLEPred;
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__0 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value;
static const lean_string_object l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__1 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value;
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__2 = (const lean_object*)&l___private_Lean_Expr_0__Lean_intLTPred___closed__2_value;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__3;
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intLTPred___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intLTPred;
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Expr_0__Lean_intEqPred___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_intEqPred;
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkIntDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_mkIntDvd___closed__0 = (const lean_object*)&l_Lean_mkIntDvd___closed__0_value;
static const lean_string_object l_Lean_mkIntDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_mkIntDvd___closed__1 = (const lean_object*)&l_Lean_mkIntDvd___closed__1_value;
static const lean_ctor_object l_Lean_mkIntDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIntDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_mkIntDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkIntDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_mkIntDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_mkIntDvd___closed__2 = (const lean_object*)&l_Lean_mkIntDvd___closed__2_value;
static lean_once_cell_t l_Lean_mkIntDvd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntDvd___closed__3;
static const lean_string_object l_Lean_mkIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Lean_mkIntDvd___closed__4 = (const lean_object*)&l_Lean_mkIntDvd___closed__4_value;
static const lean_ctor_object l_Lean_mkIntDvd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Int_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_mkIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkIntDvd___closed__5_value_aux_0),((lean_object*)&l_Lean_mkIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l_Lean_mkIntDvd___closed__5 = (const lean_object*)&l_Lean_mkIntDvd___closed__5_value;
static lean_once_cell_t l_Lean_mkIntDvd___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntDvd___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkIntLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_mkIntLit___closed__0 = (const lean_object*)&l_Lean_mkIntLit___closed__0_value;
static const lean_ctor_object l_Lean_mkIntLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkIntLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_mkIntLit___closed__1 = (const lean_object*)&l_Lean_mkIntLit___closed__1_value;
static lean_once_cell_t l_Lean_mkIntLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntLit___closed__2;
static lean_once_cell_t l_Lean_mkIntLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkIntLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object*);
static const lean_string_object l_Lean_reflBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_reflBoolTrue___closed__0 = (const lean_object*)&l_Lean_reflBoolTrue___closed__0_value;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLHSGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_reflBoolTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_reflBoolTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_reflBoolTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_reflBoolTrue___closed__1 = (const lean_object*)&l_Lean_reflBoolTrue___closed__1_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__2;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__3;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__4;
static const lean_ctor_object l_Lean_reflBoolTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isBoolFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_reflBoolTrue___closed__5 = (const lean_object*)&l_Lean_reflBoolTrue___closed__5_value;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__6;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__7;
static lean_once_cell_t l_Lean_reflBoolTrue___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolTrue___closed__8;
LEAN_EXPORT lean_object* l_Lean_reflBoolTrue;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__0;
static lean_once_cell_t l_Lean_reflBoolFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_reflBoolFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_reflBoolFalse;
static const lean_string_object l_Lean_eagerReflBoolTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eagerReduce"};
static const lean_object* l_Lean_eagerReflBoolTrue___closed__0 = (const lean_object*)&l_Lean_eagerReflBoolTrue___closed__0_value;
static const lean_ctor_object l_Lean_eagerReflBoolTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_eagerReflBoolTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 243, 67, 12, 220, 84, 120, 222)}};
static const lean_object* l_Lean_eagerReflBoolTrue___closed__1 = (const lean_object*)&l_Lean_eagerReflBoolTrue___closed__1_value;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__2;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__3;
static lean_once_cell_t l_Lean_eagerReflBoolTrue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolTrue___closed__4;
LEAN_EXPORT lean_object* l_Lean_eagerReflBoolTrue;
static lean_once_cell_t l_Lean_eagerReflBoolFalse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolFalse___closed__0;
static lean_once_cell_t l_Lean_eagerReflBoolFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_eagerReflBoolFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_eagerReflBoolFalse;
static const lean_string_object l_Lean_Expr_replaceFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Expr.replaceFn"};
static const lean_object* l_Lean_Expr_replaceFn___closed__0 = (const lean_object*)&l_Lean_Expr_replaceFn___closed__0_value;
static const lean_string_object l_Lean_Expr_replaceFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "function application or constant expected"};
static const lean_object* l_Lean_Expr_replaceFn___closed__1 = (const lean_object*)&l_Lean_Expr_replaceFn___closed__1_value;
static lean_once_cell_t l_Lean_Expr_replaceFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_replaceFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Literal_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_val_7_);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_10_; 
v_val_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_val_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_val_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Literal_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Literal_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim___redArg(lean_object* v_t_23_, lean_object* v_natVal_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Literal_ctorElim___redArg(v_t_23_, v_natVal_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_natVal_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_natVal_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Literal_ctorElim___redArg(v_t_27_, v_natVal_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim___redArg(lean_object* v_t_31_, lean_object* v_strVal_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Literal_ctorElim___redArg(v_t_31_, v_strVal_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_strVal_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_strVal_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Literal_ctorElim___redArg(v_t_35_, v_strVal_37_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLiteral_beq(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_val_45_; lean_object* v_val_46_; uint8_t v___x_47_; 
v_val_45_ = lean_ctor_get(v_x_43_, 0);
v_val_46_ = lean_ctor_get(v_x_44_, 0);
v___x_47_ = lean_nat_dec_eq(v_val_45_, v_val_46_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
else
{
if (lean_obj_tag(v_x_44_) == 1)
{
lean_object* v_val_49_; lean_object* v_val_50_; uint8_t v___x_51_; 
v_val_49_ = lean_ctor_get(v_x_43_, 0);
v_val_50_ = lean_ctor_get(v_x_44_, 0);
v___x_51_ = lean_string_dec_eq(v_val_49_, v_val_50_);
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral_beq___boxed(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_instBEqLiteral_beq(v_x_53_, v_x_54_);
lean_dec_ref(v_x_54_);
lean_dec_ref(v_x_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_instReprLiteral_repr___closed__4(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr(lean_object* v_x_75_, lean_object* v_prec_76_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_97_; 
v_val_77_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_97_ == 0)
{
v___x_79_ = v_x_75_;
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v_x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___y_82_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1024u);
v___x_94_ = lean_nat_dec_le(v___x_93_, v_prec_76_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_82_ = v___x_95_;
goto v___jp_81_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_82_ = v___x_96_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__2));
v___x_84_ = l_Nat_reprFast(v_val_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 3);
lean_ctor_set(v___x_79_, 0, v___x_84_);
v___x_86_ = v___x_79_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_92_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_83_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
lean_inc(v___y_82_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_82_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v_prec_76_);
return v___x_91_;
}
}
}
}
else
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_118_; 
v_val_98_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_118_ == 0)
{
v___x_100_ = v_x_75_;
v_isShared_101_ = v_isSharedCheck_118_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_x_75_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_118_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___y_103_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(1024u);
v___x_115_ = lean_nat_dec_le(v___x_114_, v_prec_76_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_103_ = v___x_116_;
goto v___jp_102_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_103_ = v___x_117_;
goto v___jp_102_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_104_ = ((lean_object*)(l_Lean_instReprLiteral_repr___closed__7));
v___x_105_ = l_String_quote(v_val_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 3);
lean_ctor_set(v___x_100_, 0, v___x_105_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_113_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_104_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
lean_inc(v___y_103_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_103_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_76_);
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLiteral_repr___boxed(lean_object* v_x_119_, lean_object* v_prec_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_instReprLiteral_repr(v_x_119_, v_prec_120_);
lean_dec(v_prec_120_);
return v_res_121_;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v_val_125_; uint64_t v___x_126_; 
v_val_125_ = lean_ctor_get(v_x_124_, 0);
v___x_126_ = lean_uint64_of_nat(v_val_125_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; uint64_t v___x_128_; 
v_val_127_ = lean_ctor_get(v_x_124_, 0);
v___x_128_ = lean_string_hash(v_val_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* v_x_129_){
_start:
{
uint64_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Literal_hash(v_x_129_);
lean_dec_ref(v_x_129_);
v_r_131_ = lean_box_uint64(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_val_136_; lean_object* v_val_137_; uint8_t v___x_138_; 
v_val_136_ = lean_ctor_get(v_x_134_, 0);
v_val_137_ = lean_ctor_get(v_x_135_, 0);
v___x_138_ = lean_nat_dec_lt(v_val_136_, v_val_137_);
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
}
else
{
if (lean_obj_tag(v_x_135_) == 1)
{
lean_object* v_val_140_; lean_object* v_val_141_; uint8_t v___x_142_; 
v_val_140_ = lean_ctor_get(v_x_134_, 0);
v_val_141_ = lean_ctor_get(v_x_135_, 0);
v___x_142_ = lean_string_dec_lt(v_val_140_, v_val_141_);
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Lean_Literal_lt(v_x_144_, v_x_145_);
lean_dec_ref(v_x_145_);
lean_dec_ref(v_x_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
static lean_object* _init_l_Lean_instLTLiteral(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteral(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Literal_lt(v_a_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteral___boxed(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_instDecidableLtLiteral(v_a_152_, v_b_153_);
lean_dec_ref(v_b_153_);
lean_dec_ref(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl(uint8_t v_x_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_box(v_x_156_);
v___x_158_ = lean_obj_tag_nat(v___x_157_);
lean_dec(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorIdx___impl___boxed(lean_object* v_x_159_){
_start:
{
uint8_t v_x_4__boxed_160_; lean_object* v_res_161_; 
v_x_4__boxed_160_ = lean_unbox(v_x_159_);
v_res_161_ = l_Lean_BinderInfo_ctorIdx___impl(v_x_4__boxed_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg(lean_object* v_k_162_){
_start:
{
lean_inc(v_k_162_);
return v_k_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___redArg___boxed(lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_BinderInfo_ctorElim___redArg(v_k_163_);
lean_dec(v_k_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim(lean_object* v_motive_165_, lean_object* v_ctorIdx_166_, uint8_t v_t_167_, lean_object* v_h_168_, lean_object* v_k_169_){
_start:
{
lean_inc(v_k_169_);
return v_k_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_ctorElim___boxed(lean_object* v_motive_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = l_Lean_BinderInfo_ctorElim(v_motive_170_, v_ctorIdx_171_, v_t_boxed_175_, v_h_173_, v_k_174_);
lean_dec(v_k_174_);
lean_dec(v_ctorIdx_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg(lean_object* v_default_177_){
_start:
{
lean_inc(v_default_177_);
return v_default_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___redArg___boxed(lean_object* v_default_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_BinderInfo_default_elim___redArg(v_default_178_);
lean_dec(v_default_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_default_183_){
_start:
{
lean_inc(v_default_183_);
return v_default_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_default_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_default_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = l_Lean_BinderInfo_default_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_default_187_);
lean_dec(v_default_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg(lean_object* v_implicit_190_){
_start:
{
lean_inc(v_implicit_190_);
return v_implicit_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___redArg___boxed(lean_object* v_implicit_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_BinderInfo_implicit_elim___redArg(v_implicit_191_);
lean_dec(v_implicit_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_implicit_196_){
_start:
{
lean_inc(v_implicit_196_);
return v_implicit_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_implicit_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_implicit_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_BinderInfo_implicit_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_implicit_200_);
lean_dec(v_implicit_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg(lean_object* v_strictImplicit_203_){
_start:
{
lean_inc(v_strictImplicit_203_);
return v_strictImplicit_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___redArg___boxed(lean_object* v_strictImplicit_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_BinderInfo_strictImplicit_elim___redArg(v_strictImplicit_204_);
lean_dec(v_strictImplicit_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_strictImplicit_209_){
_start:
{
lean_inc(v_strictImplicit_209_);
return v_strictImplicit_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_strictImplicit_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_strictImplicit_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lean_BinderInfo_strictImplicit_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_strictImplicit_213_);
lean_dec(v_strictImplicit_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg(lean_object* v_instImplicit_216_){
_start:
{
lean_inc(v_instImplicit_216_);
return v_instImplicit_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___redArg___boxed(lean_object* v_instImplicit_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_BinderInfo_instImplicit_elim___redArg(v_instImplicit_217_);
lean_dec(v_instImplicit_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_instImplicit_222_){
_start:
{
lean_inc(v_instImplicit_222_);
return v_instImplicit_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_instImplicit_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_instImplicit_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_BinderInfo_instImplicit_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_instImplicit_226_);
lean_dec(v_instImplicit_226_);
return v_res_228_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo_default(void){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo(void){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t v_x_231_, uint8_t v_y_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_233_ = lean_box(v_x_231_);
v___x_234_ = lean_obj_tag_nat(v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = lean_box(v_y_232_);
v___x_236_ = lean_obj_tag_nat(v___x_235_);
lean_dec(v___x_235_);
v___x_237_ = lean_nat_dec_eq(v___x_234_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo_beq___boxed(lean_object* v_x_238_, lean_object* v_y_239_){
_start:
{
uint8_t v_x_24__boxed_240_; uint8_t v_y_25__boxed_241_; uint8_t v_res_242_; lean_object* v_r_243_; 
v_x_24__boxed_240_ = lean_unbox(v_x_238_);
v_y_25__boxed_241_ = lean_unbox(v_y_239_);
v_res_242_ = l_Lean_instBEqBinderInfo_beq(v_x_24__boxed_240_, v_y_25__boxed_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr(uint8_t v_x_258_, lean_object* v_prec_259_){
_start:
{
lean_object* v___y_261_; lean_object* v___y_268_; lean_object* v___y_275_; lean_object* v___y_282_; 
switch(v_x_258_)
{
case 0:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(1024u);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_prec_259_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_261_ = v___x_290_;
goto v___jp_260_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_261_ = v___x_291_;
goto v___jp_260_;
}
}
case 1:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1024u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v_prec_259_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_268_ = v___x_294_;
goto v___jp_267_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_268_ = v___x_295_;
goto v___jp_267_;
}
}
case 2:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v_prec_259_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_275_ = v___x_298_;
goto v___jp_274_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_275_ = v___x_299_;
goto v___jp_274_;
}
}
default: 
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_259_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_282_ = v___x_302_;
goto v___jp_281_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_282_ = v___x_303_;
goto v___jp_281_;
}
}
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__1));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_259_);
return v___x_266_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_269_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__3));
lean_inc(v___y_268_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_259_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__5));
lean_inc(v___y_275_);
v___x_277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_278_);
v___x_280_ = l_Repr_addAppParen(v___x_279_, v_prec_259_);
return v___x_280_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = ((lean_object*)(l_Lean_instReprBinderInfo_repr___closed__7));
lean_inc(v___y_282_);
v___x_284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = 0;
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_285_);
v___x_287_ = l_Repr_addAppParen(v___x_286_, v_prec_259_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo_repr___boxed(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
uint8_t v_x_221__boxed_306_; lean_object* v_res_307_; 
v_x_221__boxed_306_ = lean_unbox(v_x_304_);
v_res_307_ = l_Lean_instReprBinderInfo_repr(v_x_221__boxed_306_, v_prec_305_);
lean_dec(v_prec_305_);
return v_res_307_;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t v_x_310_){
_start:
{
switch(v_x_310_)
{
case 0:
{
uint64_t v___x_311_; 
v___x_311_ = 947ULL;
return v___x_311_;
}
case 1:
{
uint64_t v___x_312_; 
v___x_312_ = 1019ULL;
return v___x_312_;
}
case 2:
{
uint64_t v___x_313_; 
v___x_313_ = 1087ULL;
return v___x_313_;
}
default: 
{
uint64_t v___x_314_; 
v___x_314_ = 1153ULL;
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* v_x_315_){
_start:
{
uint8_t v_x_52__boxed_316_; uint64_t v_res_317_; lean_object* v_r_318_; 
v_x_52__boxed_316_ = lean_unbox(v_x_315_);
v_res_317_ = l_Lean_BinderInfo_hash(v_x_52__boxed_316_);
v_r_318_ = lean_box_uint64(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t v_x_319_){
_start:
{
switch(v_x_319_)
{
case 1:
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
case 2:
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
case 3:
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
default: 
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* v_x_324_){
_start:
{
uint8_t v_x_27__boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_x_27__boxed_325_ = lean_unbox(v_x_324_);
v_res_326_ = l_Lean_BinderInfo_isExplicit(v_x_27__boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t v_x_330_){
_start:
{
if (v_x_330_ == 3)
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_x_17__boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_x_17__boxed_334_ = lean_unbox(v_x_333_);
v_res_335_ = l_Lean_BinderInfo_isInstImplicit(v_x_17__boxed_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t v_x_337_){
_start:
{
if (v_x_337_ == 1)
{
uint8_t v___x_338_; 
v___x_338_ = 1;
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 0;
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* v_x_340_){
_start:
{
uint8_t v_x_17__boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_x_17__boxed_341_ = lean_unbox(v_x_340_);
v_res_342_ = l_Lean_BinderInfo_isImplicit(v_x_17__boxed_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t v_x_344_){
_start:
{
if (v_x_344_ == 2)
{
uint8_t v___x_345_; 
v___x_345_ = 1;
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* v_x_347_){
_start:
{
uint8_t v_x_17__boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v_x_17__boxed_348_ = lean_unbox(v_x_347_);
v_res_349_ = l_Lean_BinderInfo_isStrictImplicit(v_x_17__boxed_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_MData_empty(void){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1___aux__1(void){
_start:
{
uint64_t v___x_352_; 
v___x_352_ = 0ULL;
return v___x_352_;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1(void){
_start:
{
uint64_t v___x_353_; 
v___x_353_ = 0ULL;
return v___x_353_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t v_c_354_){
_start:
{
uint32_t v___x_355_; uint64_t v___x_356_; 
v___x_355_ = lean_uint64_to_uint32(v_c_354_);
v___x_356_ = lean_uint32_to_uint64(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* v_c_357_){
_start:
{
uint64_t v_c_boxed_358_; uint64_t v_res_359_; lean_object* v_r_360_; 
v_c_boxed_358_ = lean_unbox_uint64(v_c_357_);
lean_dec_ref(v_c_357_);
v_res_359_ = l_Lean_Expr_Data_hash(v_c_boxed_358_);
v_r_360_ = lean_box_uint64(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t v_c_363_){
_start:
{
uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint8_t v___x_368_; 
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v_c_363_, v___x_364_);
v___x_366_ = 255ULL;
v___x_367_ = lean_uint64_land(v___x_365_, v___x_366_);
v___x_368_ = lean_uint64_to_uint8(v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* v_c_369_){
_start:
{
uint64_t v_c_boxed_370_; uint8_t v_res_371_; lean_object* v_r_372_; 
v_c_boxed_370_ = lean_unbox_uint64(v_c_369_);
lean_dec_ref(v_c_369_);
v_res_371_ = l_Lean_Expr_Data_approxDepth(v_c_boxed_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t v_c_373_){
_start:
{
uint64_t v___x_374_; uint64_t v___x_375_; uint32_t v___x_376_; 
v___x_374_ = 44ULL;
v___x_375_ = lean_uint64_shift_right(v_c_373_, v___x_374_);
v___x_376_ = lean_uint64_to_uint32(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* v_c_377_){
_start:
{
uint64_t v_c_boxed_378_; uint32_t v_res_379_; lean_object* v_r_380_; 
v_c_boxed_378_ = lean_unbox_uint64(v_c_377_);
lean_dec_ref(v_c_377_);
v_res_379_ = l_Lean_Expr_Data_looseBVarRange(v_c_boxed_378_);
v_r_380_ = lean_box_uint32(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t v_c_381_){
_start:
{
uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint8_t v___x_386_; 
v___x_382_ = 40ULL;
v___x_383_ = lean_uint64_shift_right(v_c_381_, v___x_382_);
v___x_384_ = 1ULL;
v___x_385_ = lean_uint64_land(v___x_383_, v___x_384_);
v___x_386_ = lean_uint64_dec_eq(v___x_385_, v___x_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* v_c_387_){
_start:
{
uint64_t v_c_boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_c_boxed_388_ = lean_unbox_uint64(v_c_387_);
lean_dec_ref(v_c_387_);
v_res_389_ = l_Lean_Expr_Data_hasFVar(v_c_boxed_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t v_c_391_){
_start:
{
uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint8_t v___x_396_; 
v___x_392_ = 41ULL;
v___x_393_ = lean_uint64_shift_right(v_c_391_, v___x_392_);
v___x_394_ = 1ULL;
v___x_395_ = lean_uint64_land(v___x_393_, v___x_394_);
v___x_396_ = lean_uint64_dec_eq(v___x_395_, v___x_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* v_c_397_){
_start:
{
uint64_t v_c_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_c_boxed_398_ = lean_unbox_uint64(v_c_397_);
lean_dec_ref(v_c_397_);
v_res_399_ = l_Lean_Expr_Data_hasExprMVar(v_c_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t v_c_401_){
_start:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint8_t v___x_406_; 
v___x_402_ = 42ULL;
v___x_403_ = lean_uint64_shift_right(v_c_401_, v___x_402_);
v___x_404_ = 1ULL;
v___x_405_ = lean_uint64_land(v___x_403_, v___x_404_);
v___x_406_ = lean_uint64_dec_eq(v___x_405_, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* v_c_407_){
_start:
{
uint64_t v_c_boxed_408_; uint8_t v_res_409_; lean_object* v_r_410_; 
v_c_boxed_408_ = lean_unbox_uint64(v_c_407_);
lean_dec_ref(v_c_407_);
v_res_409_ = l_Lean_Expr_Data_hasLevelMVar(v_c_boxed_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t v_c_411_){
_start:
{
uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint8_t v___x_416_; 
v___x_412_ = 43ULL;
v___x_413_ = lean_uint64_shift_right(v_c_411_, v___x_412_);
v___x_414_ = 1ULL;
v___x_415_ = lean_uint64_land(v___x_413_, v___x_414_);
v___x_416_ = lean_uint64_dec_eq(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* v_c_417_){
_start:
{
uint64_t v_c_boxed_418_; uint8_t v_res_419_; lean_object* v_r_420_; 
v_c_boxed_418_ = lean_unbox_uint64(v_c_417_);
lean_dec_ref(v_c_417_);
v_res_419_ = l_Lean_Expr_Data_hasLevelParam(v_c_boxed_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* v_a_00___x40___internal___hyg_422_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_423_; uint64_t v_res_424_; lean_object* v_r_425_; 
v_a_00___x40___internal___hyg_1__boxed_423_ = lean_unbox(v_a_00___x40___internal___hyg_422_);
v_res_424_ = lean_uint8_to_uint64(v_a_00___x40___internal___hyg_1__boxed_423_);
v_r_425_ = lean_box_uint64(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* v_h_433_, lean_object* v_looseBVarRange_434_, lean_object* v_approxDepth_435_, lean_object* v_hasFVar_436_, lean_object* v_hasExprMVar_437_, lean_object* v_hasLevelMVar_438_, lean_object* v_hasLevelParam_439_){
_start:
{
uint64_t v_h_boxed_440_; uint32_t v_approxDepth_boxed_441_; uint8_t v_hasFVar_boxed_442_; uint8_t v_hasExprMVar_boxed_443_; uint8_t v_hasLevelMVar_boxed_444_; uint8_t v_hasLevelParam_boxed_445_; uint64_t v_res_446_; lean_object* v_r_447_; 
v_h_boxed_440_ = lean_unbox_uint64(v_h_433_);
lean_dec_ref(v_h_433_);
v_approxDepth_boxed_441_ = lean_unbox_uint32(v_approxDepth_435_);
lean_dec(v_approxDepth_435_);
v_hasFVar_boxed_442_ = lean_unbox(v_hasFVar_436_);
v_hasExprMVar_boxed_443_ = lean_unbox(v_hasExprMVar_437_);
v_hasLevelMVar_boxed_444_ = lean_unbox(v_hasLevelMVar_438_);
v_hasLevelParam_boxed_445_ = lean_unbox(v_hasLevelParam_439_);
v_res_446_ = lean_expr_mk_data(v_h_boxed_440_, v_looseBVarRange_434_, v_approxDepth_boxed_441_, v_hasFVar_boxed_442_, v_hasExprMVar_boxed_443_, v_hasLevelMVar_boxed_444_, v_hasLevelParam_boxed_445_);
v_r_447_ = lean_box_uint64(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* v_fData_450_, lean_object* v_aData_451_){
_start:
{
uint64_t v_fData_boxed_452_; uint64_t v_aData_boxed_453_; uint64_t v_res_454_; lean_object* v_r_455_; 
v_fData_boxed_452_ = lean_unbox_uint64(v_fData_450_);
lean_dec_ref(v_fData_450_);
v_aData_boxed_453_ = lean_unbox_uint64(v_aData_451_);
lean_dec_ref(v_aData_451_);
v_res_454_ = lean_expr_mk_app_data(v_fData_boxed_452_, v_aData_boxed_453_);
v_r_455_ = lean_box_uint64(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t v_h_456_, lean_object* v_looseBVarRange_457_, uint32_t v_approxDepth_458_, uint8_t v_hasFVar_459_, uint8_t v_hasExprMVar_460_, uint8_t v_hasLevelMVar_461_, uint8_t v_hasLevelParam_462_){
_start:
{
uint64_t v___x_463_; 
v___x_463_ = lean_expr_mk_data(v_h_456_, v_looseBVarRange_457_, v_approxDepth_458_, v_hasFVar_459_, v_hasExprMVar_460_, v_hasLevelMVar_461_, v_hasLevelParam_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* v_h_464_, lean_object* v_looseBVarRange_465_, lean_object* v_approxDepth_466_, lean_object* v_hasFVar_467_, lean_object* v_hasExprMVar_468_, lean_object* v_hasLevelMVar_469_, lean_object* v_hasLevelParam_470_){
_start:
{
uint64_t v_h_boxed_471_; uint32_t v_approxDepth_boxed_472_; uint8_t v_hasFVar_boxed_473_; uint8_t v_hasExprMVar_boxed_474_; uint8_t v_hasLevelMVar_boxed_475_; uint8_t v_hasLevelParam_boxed_476_; uint64_t v_res_477_; lean_object* v_r_478_; 
v_h_boxed_471_ = lean_unbox_uint64(v_h_464_);
lean_dec_ref(v_h_464_);
v_approxDepth_boxed_472_ = lean_unbox_uint32(v_approxDepth_466_);
lean_dec(v_approxDepth_466_);
v_hasFVar_boxed_473_ = lean_unbox(v_hasFVar_467_);
v_hasExprMVar_boxed_474_ = lean_unbox(v_hasExprMVar_468_);
v_hasLevelMVar_boxed_475_ = lean_unbox(v_hasLevelMVar_469_);
v_hasLevelParam_boxed_476_ = lean_unbox(v_hasLevelParam_470_);
v_res_477_ = l_Lean_Expr_mkDataForBinder(v_h_boxed_471_, v_looseBVarRange_465_, v_approxDepth_boxed_472_, v_hasFVar_boxed_473_, v_hasExprMVar_boxed_474_, v_hasLevelMVar_boxed_475_, v_hasLevelParam_boxed_476_);
v_r_478_ = lean_box_uint64(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t v_h_479_, lean_object* v_looseBVarRange_480_, uint32_t v_approxDepth_481_, uint8_t v_hasFVar_482_, uint8_t v_hasExprMVar_483_, uint8_t v_hasLevelMVar_484_, uint8_t v_hasLevelParam_485_){
_start:
{
uint64_t v___x_486_; 
v___x_486_ = lean_expr_mk_data(v_h_479_, v_looseBVarRange_480_, v_approxDepth_481_, v_hasFVar_482_, v_hasExprMVar_483_, v_hasLevelMVar_484_, v_hasLevelParam_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* v_h_487_, lean_object* v_looseBVarRange_488_, lean_object* v_approxDepth_489_, lean_object* v_hasFVar_490_, lean_object* v_hasExprMVar_491_, lean_object* v_hasLevelMVar_492_, lean_object* v_hasLevelParam_493_){
_start:
{
uint64_t v_h_boxed_494_; uint32_t v_approxDepth_boxed_495_; uint8_t v_hasFVar_boxed_496_; uint8_t v_hasExprMVar_boxed_497_; uint8_t v_hasLevelMVar_boxed_498_; uint8_t v_hasLevelParam_boxed_499_; uint64_t v_res_500_; lean_object* v_r_501_; 
v_h_boxed_494_ = lean_unbox_uint64(v_h_487_);
lean_dec_ref(v_h_487_);
v_approxDepth_boxed_495_ = lean_unbox_uint32(v_approxDepth_489_);
lean_dec(v_approxDepth_489_);
v_hasFVar_boxed_496_ = lean_unbox(v_hasFVar_490_);
v_hasExprMVar_boxed_497_ = lean_unbox(v_hasExprMVar_491_);
v_hasLevelMVar_boxed_498_ = lean_unbox(v_hasLevelMVar_492_);
v_hasLevelParam_boxed_499_ = lean_unbox(v_hasLevelParam_493_);
v_res_500_ = l_Lean_Expr_mkDataForLet(v_h_boxed_494_, v_looseBVarRange_488_, v_approxDepth_boxed_495_, v_hasFVar_boxed_496_, v_hasExprMVar_boxed_497_, v_hasLevelMVar_boxed_498_, v_hasLevelParam_boxed_499_);
v_r_501_ = lean_box_uint64(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0(uint64_t v_v_510_, lean_object* v_prec_511_){
_start:
{
lean_object* v_r_513_; lean_object* v_r_517_; lean_object* v_r_526_; lean_object* v_r_535_; lean_object* v_r_544_; lean_object* v___x_555_; uint64_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_r_559_; uint32_t v___x_560_; uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_555_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__6));
v___x_556_ = l_Lean_Expr_Data_hash(v_v_510_);
v___x_557_ = lean_uint64_to_nat(v___x_556_);
v___x_558_ = l_Nat_reprFast(v___x_557_);
v_r_559_ = lean_string_append(v___x_555_, v___x_558_);
lean_dec_ref(v___x_558_);
v___x_560_ = l_Lean_Expr_Data_looseBVarRange(v_v_510_);
v___x_561_ = 0;
v___x_562_ = lean_uint32_dec_eq(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_r_569_; 
v___x_563_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__7));
v___x_564_ = lean_string_append(v_r_559_, v___x_563_);
v___x_565_ = lean_uint32_to_nat(v___x_560_);
v___x_566_ = l_Nat_reprFast(v___x_565_);
v___x_567_ = lean_string_append(v___x_564_, v___x_566_);
lean_dec_ref(v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_569_ = lean_string_append(v___x_567_, v___x_568_);
v_r_544_ = v_r_569_;
goto v___jp_543_;
}
else
{
v_r_544_ = v_r_559_;
goto v___jp_543_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_514_, 0, v_r_513_);
v___x_515_ = l_Repr_addAppParen(v___x_514_, v_prec_511_);
return v___x_515_;
}
v___jp_516_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Expr_Data_hasLevelMVar(v_v_510_);
if (v___x_518_ == 0)
{
v_r_513_ = v_r_517_;
goto v___jp_512_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_r_524_; 
v___x_519_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__0));
v___x_520_ = lean_string_append(v_r_517_, v___x_519_);
v___x_521_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_524_ = lean_string_append(v___x_522_, v___x_523_);
v_r_513_ = v_r_524_;
goto v___jp_512_;
}
}
v___jp_525_:
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Expr_Data_hasExprMVar(v_v_510_);
if (v___x_527_ == 0)
{
v_r_517_ = v_r_526_;
goto v___jp_516_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_r_533_; 
v___x_528_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__3));
v___x_529_ = lean_string_append(v_r_526_, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_531_ = lean_string_append(v___x_529_, v___x_530_);
v___x_532_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_533_ = lean_string_append(v___x_531_, v___x_532_);
v_r_517_ = v_r_533_;
goto v___jp_516_;
}
}
v___jp_534_:
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Expr_Data_hasFVar(v_v_510_);
if (v___x_536_ == 0)
{
v_r_526_ = v_r_535_;
goto v___jp_525_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_r_542_; 
v___x_537_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__4));
v___x_538_ = lean_string_append(v_r_535_, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__1));
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
v___x_541_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_542_ = lean_string_append(v___x_540_, v___x_541_);
v_r_526_ = v_r_542_;
goto v___jp_525_;
}
}
v___jp_543_:
{
uint8_t v___x_545_; uint8_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = l_Lean_Expr_Data_approxDepth(v_v_510_);
v___x_546_ = 0;
v___x_547_ = lean_uint8_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_r_554_; 
v___x_548_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__5));
v___x_549_ = lean_string_append(v_r_544_, v___x_548_);
v___x_550_ = lean_uint8_to_nat(v___x_545_);
v___x_551_ = l_Nat_reprFast(v___x_550_);
v___x_552_ = lean_string_append(v___x_549_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l_Lean_instReprData__1___lam__0___closed__2));
v_r_554_ = lean_string_append(v___x_552_, v___x_553_);
v_r_535_ = v_r_554_;
goto v___jp_534_;
}
else
{
v_r_535_ = v_r_544_;
goto v___jp_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lam__0___boxed(lean_object* v_v_570_, lean_object* v_prec_571_){
_start:
{
uint64_t v_v_boxed_572_; lean_object* v_res_573_; 
v_v_boxed_572_ = lean_unbox_uint64(v_v_570_);
lean_dec_ref(v_v_570_);
v_res_573_ = l_Lean_instReprData__1___lam__0(v_v_boxed_572_, v_prec_571_);
lean_dec(v_prec_571_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId_default(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId(void){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
return v___x_577_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqFVarId_beq(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_name_eq(v_x_578_, v_x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Lean_instBEqFVarId_beq(v_x_581_, v_x_582_);
lean_dec(v_x_582_);
lean_dec(v_x_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableFVarId_hash(lean_object* v_x_587_){
_start:
{
uint64_t v___x_588_; 
v___x_588_ = 0ULL;
if (lean_obj_tag(v_x_587_) == 0)
{
uint64_t v___x_589_; 
v___x_589_ = 8934034000889494153ULL;
return v___x_589_;
}
else
{
uint64_t v_hash_590_; uint64_t v___x_591_; 
v_hash_590_ = lean_ctor_get_uint64(v_x_587_, sizeof(void*)*2);
v___x_591_ = lean_uint64_mix_hash(v___x_588_, v_hash_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object* v_x_592_){
_start:
{
uint64_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Lean_instHashableFVarId_hash(v_x_592_);
lean_dec(v_x_592_);
v_r_594_ = lean_box_uint64(v_res_593_);
return v_r_594_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(1);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdSet(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(1);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_box(1);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdSet(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(1);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___aux__1(lean_object* v_e_604_){
_start:
{
lean_object* v___f_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___f_605_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_606_ = lean_box(1);
lean_inc(v_e_604_);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___f_605_, v_e_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_605_, v_e_604_, v___x_608_, v___x_606_);
return v___x_609_;
}
else
{
lean_dec(v_e_604_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object* v_k_610_, lean_object* v_v_611_, lean_object* v_t_612_){
_start:
{
if (lean_obj_tag(v_t_612_) == 0)
{
lean_object* v_size_613_; lean_object* v_k_614_; lean_object* v_v_615_; lean_object* v_l_616_; lean_object* v_r_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_897_; 
v_size_613_ = lean_ctor_get(v_t_612_, 0);
v_k_614_ = lean_ctor_get(v_t_612_, 1);
v_v_615_ = lean_ctor_get(v_t_612_, 2);
v_l_616_ = lean_ctor_get(v_t_612_, 3);
v_r_617_ = lean_ctor_get(v_t_612_, 4);
v_isSharedCheck_897_ = !lean_is_exclusive(v_t_612_);
if (v_isSharedCheck_897_ == 0)
{
v___x_619_ = v_t_612_;
v_isShared_620_ = v_isSharedCheck_897_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_r_617_);
lean_inc(v_l_616_);
lean_inc(v_v_615_);
lean_inc(v_k_614_);
lean_inc(v_size_613_);
lean_dec(v_t_612_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_897_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___x_621_; 
v___x_621_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_610_, v_k_614_);
switch(v___x_621_)
{
case 0:
{
lean_object* v_impl_622_; lean_object* v___x_623_; 
lean_dec(v_size_613_);
v_impl_622_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_610_, v_v_611_, v_l_616_);
v___x_623_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_617_) == 0)
{
lean_object* v_size_624_; lean_object* v_size_625_; lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v_l_628_; lean_object* v_r_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_size_624_ = lean_ctor_get(v_r_617_, 0);
v_size_625_ = lean_ctor_get(v_impl_622_, 0);
v_k_626_ = lean_ctor_get(v_impl_622_, 1);
v_v_627_ = lean_ctor_get(v_impl_622_, 2);
v_l_628_ = lean_ctor_get(v_impl_622_, 3);
v_r_629_ = lean_ctor_get(v_impl_622_, 4);
lean_inc(v_r_629_);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_nat_mul(v___x_630_, v_size_624_);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v_size_625_);
lean_dec(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_r_629_);
v___x_633_ = lean_nat_add(v___x_623_, v_size_625_);
v___x_634_ = lean_nat_add(v___x_633_, v_size_624_);
lean_dec(v___x_633_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 3, v_impl_622_);
lean_ctor_set(v___x_619_, 0, v___x_634_);
v___x_636_ = v___x_619_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_impl_622_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_r_617_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_703_; 
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_inc(v_size_625_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_impl_622_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; 
v_unused_704_ = lean_ctor_get(v_impl_622_, 4);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_impl_622_, 3);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_impl_622_, 2);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_impl_622_, 1);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_impl_622_, 0);
lean_dec(v_unused_708_);
v___x_639_ = v_impl_622_;
v_isShared_640_ = v_isSharedCheck_703_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_impl_622_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_703_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_size_641_; lean_object* v_size_642_; lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_size_641_ = lean_ctor_get(v_l_628_, 0);
v_size_642_ = lean_ctor_get(v_r_629_, 0);
v_k_643_ = lean_ctor_get(v_r_629_, 1);
v_v_644_ = lean_ctor_get(v_r_629_, 2);
v_l_645_ = lean_ctor_get(v_r_629_, 3);
v_r_646_ = lean_ctor_get(v_r_629_, 4);
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_nat_mul(v___x_647_, v_size_641_);
v___x_649_ = lean_nat_dec_lt(v_size_642_, v___x_648_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_678_; 
lean_inc(v_r_646_);
lean_inc(v_l_645_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
v_isSharedCheck_678_ = !lean_is_exclusive(v_r_629_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; lean_object* v_unused_680_; lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_679_ = lean_ctor_get(v_r_629_, 4);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_r_629_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_r_629_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_r_629_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_629_, 0);
lean_dec(v_unused_683_);
v___x_651_ = v_r_629_;
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
else
{
lean_dec(v_r_629_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___x_666_; lean_object* v___y_668_; 
v___x_653_ = lean_nat_add(v___x_623_, v_size_625_);
lean_dec(v_size_625_);
v___x_654_ = lean_nat_add(v___x_653_, v_size_624_);
lean_dec(v___x_653_);
v___x_666_ = lean_nat_add(v___x_623_, v_size_641_);
if (lean_obj_tag(v_l_645_) == 0)
{
lean_object* v_size_676_; 
v_size_676_ = lean_ctor_get(v_l_645_, 0);
lean_inc(v_size_676_);
v___y_668_ = v_size_676_;
goto v___jp_667_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_unsigned_to_nat(0u);
v___y_668_ = v___x_677_;
goto v___jp_667_;
}
v___jp_655_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_nat_add(v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_r_617_);
lean_ctor_set(v___x_651_, 3, v_r_646_);
lean_ctor_set(v___x_651_, 2, v_v_615_);
lean_ctor_set(v___x_651_, 1, v_k_614_);
lean_ctor_set(v___x_651_, 0, v___x_659_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_r_617_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v___x_661_);
lean_ctor_set(v___x_639_, 3, v___y_656_);
lean_ctor_set(v___x_639_, 2, v_v_644_);
lean_ctor_set(v___x_639_, 1, v_k_643_);
lean_ctor_set(v___x_639_, 0, v___x_654_);
v___x_663_ = v___x_639_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v___y_656_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_nat_add(v___x_666_, v___y_668_);
lean_dec(v___y_668_);
lean_dec(v___x_666_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_l_645_);
lean_ctor_set(v___x_619_, 3, v_l_628_);
lean_ctor_set(v___x_619_, 2, v_v_627_);
lean_ctor_set(v___x_619_, 1, v_k_626_);
lean_ctor_set(v___x_619_, 0, v___x_669_);
v___x_671_ = v___x_619_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_l_645_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_nat_add(v___x_623_, v_size_624_);
if (lean_obj_tag(v_r_646_) == 0)
{
lean_object* v_size_673_; 
v_size_673_ = lean_ctor_get(v_r_646_, 0);
lean_inc(v_size_673_);
v___y_656_ = v___x_671_;
v___y_657_ = v___x_672_;
v___y_658_ = v_size_673_;
goto v___jp_655_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___y_656_ = v___x_671_;
v___y_657_ = v___x_672_;
v___y_658_ = v___x_674_;
goto v___jp_655_;
}
}
}
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
lean_del_object(v___x_619_);
v___x_684_ = lean_nat_add(v___x_623_, v_size_625_);
lean_dec(v_size_625_);
v___x_685_ = lean_nat_add(v___x_684_, v_size_624_);
lean_dec(v___x_684_);
v___x_686_ = lean_nat_add(v___x_623_, v_size_624_);
v___x_687_ = lean_nat_add(v___x_686_, v_size_642_);
lean_dec(v___x_686_);
lean_inc_ref(v_r_617_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 4, v_r_617_);
lean_ctor_set(v___x_639_, 3, v_r_629_);
lean_ctor_set(v___x_639_, 2, v_v_615_);
lean_ctor_set(v___x_639_, 1, v_k_614_);
lean_ctor_set(v___x_639_, 0, v___x_687_);
v___x_689_ = v___x_639_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_r_617_);
v___x_689_ = v_reuseFailAlloc_702_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_isSharedCheck_696_ = !lean_is_exclusive(v_r_617_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_697_ = lean_ctor_get(v_r_617_, 4);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_617_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_r_617_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_r_617_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_r_617_, 0);
lean_dec(v_unused_701_);
v___x_691_ = v_r_617_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_r_617_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 4, v___x_689_);
lean_ctor_set(v___x_691_, 3, v_l_628_);
lean_ctor_set(v___x_691_, 2, v_v_627_);
lean_ctor_set(v___x_691_, 1, v_k_626_);
lean_ctor_set(v___x_691_, 0, v___x_685_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_626_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_627_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_709_; 
v_l_709_ = lean_ctor_get(v_impl_622_, 3);
if (lean_obj_tag(v_l_709_) == 0)
{
lean_object* v_r_710_; lean_object* v_k_711_; lean_object* v_v_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
lean_inc_ref(v_l_709_);
v_r_710_ = lean_ctor_get(v_impl_622_, 4);
v_k_711_ = lean_ctor_get(v_impl_622_, 1);
v_v_712_ = lean_ctor_get(v_impl_622_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_impl_622_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_724_ = lean_ctor_get(v_impl_622_, 3);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_impl_622_, 0);
lean_dec(v_unused_725_);
v___x_714_ = v_impl_622_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_r_710_);
lean_inc(v_v_712_);
lean_inc(v_k_711_);
lean_dec(v_impl_622_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 3, v_r_710_);
lean_ctor_set(v___x_714_, 2, v_v_615_);
lean_ctor_set(v___x_714_, 1, v_k_614_);
lean_ctor_set(v___x_714_, 0, v___x_623_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_r_710_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_r_710_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v___x_718_);
lean_ctor_set(v___x_619_, 3, v_l_709_);
lean_ctor_set(v___x_619_, 2, v_v_712_);
lean_ctor_set(v___x_619_, 1, v_k_711_);
lean_ctor_set(v___x_619_, 0, v___x_716_);
v___x_720_ = v___x_619_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_712_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_l_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_r_726_; 
v_r_726_ = lean_ctor_get(v_impl_622_, 4);
lean_inc(v_r_726_);
if (lean_obj_tag(v_r_726_) == 0)
{
lean_object* v_k_727_; lean_object* v_v_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_751_; 
lean_inc(v_l_709_);
v_k_727_ = lean_ctor_get(v_impl_622_, 1);
v_v_728_ = lean_ctor_get(v_impl_622_, 2);
v_isSharedCheck_751_ = !lean_is_exclusive(v_impl_622_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_752_ = lean_ctor_get(v_impl_622_, 4);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_impl_622_, 3);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_impl_622_, 0);
lean_dec(v_unused_754_);
v___x_730_ = v_impl_622_;
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_v_728_);
lean_inc(v_k_727_);
lean_dec(v_impl_622_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_751_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_k_732_; lean_object* v_v_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_747_; 
v_k_732_ = lean_ctor_get(v_r_726_, 1);
v_v_733_ = lean_ctor_get(v_r_726_, 2);
v_isSharedCheck_747_ = !lean_is_exclusive(v_r_726_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_748_ = lean_ctor_get(v_r_726_, 4);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_r_726_, 3);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_r_726_, 0);
lean_dec(v_unused_750_);
v___x_735_ = v_r_726_;
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_v_733_);
lean_inc(v_k_732_);
lean_dec(v_r_726_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(3u);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v_l_709_);
lean_ctor_set(v___x_735_, 3, v_l_709_);
lean_ctor_set(v___x_735_, 2, v_v_728_);
lean_ctor_set(v___x_735_, 1, v_k_727_);
lean_ctor_set(v___x_735_, 0, v___x_623_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_l_709_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_l_709_);
v___x_739_ = v_reuseFailAlloc_746_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_l_709_);
lean_ctor_set(v___x_730_, 2, v_v_615_);
lean_ctor_set(v___x_730_, 1, v_k_614_);
lean_ctor_set(v___x_730_, 0, v___x_623_);
v___x_741_ = v___x_730_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_l_709_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_l_709_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v___x_741_);
lean_ctor_set(v___x_619_, 3, v___x_739_);
lean_ctor_set(v___x_619_, 2, v_v_733_);
lean_ctor_set(v___x_619_, 1, v_k_732_);
lean_ctor_set(v___x_619_, 0, v___x_737_);
v___x_743_ = v___x_619_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_unsigned_to_nat(2u);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_r_726_);
lean_ctor_set(v___x_619_, 3, v_impl_622_);
lean_ctor_set(v___x_619_, 0, v___x_755_);
v___x_757_ = v___x_619_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_impl_622_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_r_726_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
case 1:
{
lean_object* v___x_760_; 
lean_dec(v_v_615_);
lean_dec(v_k_614_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 2, v_v_611_);
lean_ctor_set(v___x_619_, 1, v_k_610_);
v___x_760_ = v___x_619_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_size_613_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_610_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_611_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_r_617_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
default: 
{
lean_object* v_impl_762_; lean_object* v___x_763_; 
lean_dec(v_size_613_);
v_impl_762_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_610_, v_v_611_, v_r_617_);
v___x_763_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_616_) == 0)
{
lean_object* v_size_764_; lean_object* v_size_765_; lean_object* v_k_766_; lean_object* v_v_767_; lean_object* v_l_768_; lean_object* v_r_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_size_764_ = lean_ctor_get(v_l_616_, 0);
v_size_765_ = lean_ctor_get(v_impl_762_, 0);
v_k_766_ = lean_ctor_get(v_impl_762_, 1);
v_v_767_ = lean_ctor_get(v_impl_762_, 2);
v_l_768_ = lean_ctor_get(v_impl_762_, 3);
lean_inc(v_l_768_);
v_r_769_ = lean_ctor_get(v_impl_762_, 4);
v___x_770_ = lean_unsigned_to_nat(3u);
v___x_771_ = lean_nat_mul(v___x_770_, v_size_764_);
v___x_772_ = lean_nat_dec_lt(v___x_771_, v_size_765_);
lean_dec(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec(v_l_768_);
v___x_773_ = lean_nat_add(v___x_763_, v_size_764_);
v___x_774_ = lean_nat_add(v___x_773_, v_size_765_);
lean_dec(v___x_773_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_impl_762_);
lean_ctor_set(v___x_619_, 0, v___x_774_);
v___x_776_ = v___x_619_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_impl_762_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_841_; 
lean_inc(v_r_769_);
lean_inc(v_v_767_);
lean_inc(v_k_766_);
lean_inc(v_size_765_);
v_isSharedCheck_841_ = !lean_is_exclusive(v_impl_762_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_842_ = lean_ctor_get(v_impl_762_, 4);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_impl_762_, 3);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_impl_762_, 2);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_impl_762_, 1);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_impl_762_, 0);
lean_dec(v_unused_846_);
v___x_779_ = v_impl_762_;
v_isShared_780_ = v_isSharedCheck_841_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_impl_762_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_841_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_size_781_; lean_object* v_k_782_; lean_object* v_v_783_; lean_object* v_l_784_; lean_object* v_r_785_; lean_object* v_size_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_size_781_ = lean_ctor_get(v_l_768_, 0);
v_k_782_ = lean_ctor_get(v_l_768_, 1);
v_v_783_ = lean_ctor_get(v_l_768_, 2);
v_l_784_ = lean_ctor_get(v_l_768_, 3);
v_r_785_ = lean_ctor_get(v_l_768_, 4);
v_size_786_ = lean_ctor_get(v_r_769_, 0);
v___x_787_ = lean_unsigned_to_nat(2u);
v___x_788_ = lean_nat_mul(v___x_787_, v_size_786_);
v___x_789_ = lean_nat_dec_lt(v_size_781_, v___x_788_);
lean_dec(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_817_; 
lean_inc(v_r_785_);
lean_inc(v_l_784_);
lean_inc(v_v_783_);
lean_inc(v_k_782_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_l_768_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_818_ = lean_ctor_get(v_l_768_, 4);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_768_, 3);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_l_768_, 2);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_l_768_, 1);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_l_768_, 0);
lean_dec(v_unused_822_);
v___x_791_ = v_l_768_;
v_isShared_792_ = v_isSharedCheck_817_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_l_768_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_817_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_807_; 
v___x_793_ = lean_nat_add(v___x_763_, v_size_764_);
v___x_794_ = lean_nat_add(v___x_793_, v_size_765_);
lean_dec(v_size_765_);
if (lean_obj_tag(v_l_784_) == 0)
{
lean_object* v_size_815_; 
v_size_815_ = lean_ctor_get(v_l_784_, 0);
lean_inc(v_size_815_);
v___y_807_ = v_size_815_;
goto v___jp_806_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = lean_unsigned_to_nat(0u);
v___y_807_ = v___x_816_;
goto v___jp_806_;
}
v___jp_795_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_nat_add(v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec(v___y_797_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_r_769_);
lean_ctor_set(v___x_791_, 3, v_r_785_);
lean_ctor_set(v___x_791_, 2, v_v_767_);
lean_ctor_set(v___x_791_, 1, v_k_766_);
lean_ctor_set(v___x_791_, 0, v___x_799_);
v___x_801_ = v___x_791_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_766_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_r_785_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_r_769_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v___x_801_);
lean_ctor_set(v___x_779_, 3, v___y_796_);
lean_ctor_set(v___x_779_, 2, v_v_783_);
lean_ctor_set(v___x_779_, 1, v_k_782_);
lean_ctor_set(v___x_779_, 0, v___x_794_);
v___x_803_ = v___x_779_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_782_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_783_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v___y_796_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_nat_add(v___x_793_, v___y_807_);
lean_dec(v___y_807_);
lean_dec(v___x_793_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_l_784_);
lean_ctor_set(v___x_619_, 0, v___x_808_);
v___x_810_ = v___x_619_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_l_784_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_nat_add(v___x_763_, v_size_786_);
if (lean_obj_tag(v_r_785_) == 0)
{
lean_object* v_size_812_; 
v_size_812_ = lean_ctor_get(v_r_785_, 0);
lean_inc(v_size_812_);
v___y_796_ = v___x_810_;
v___y_797_ = v___x_811_;
v___y_798_ = v_size_812_;
goto v___jp_795_;
}
else
{
lean_object* v___x_813_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___y_796_ = v___x_810_;
v___y_797_ = v___x_811_;
v___y_798_ = v___x_813_;
goto v___jp_795_;
}
}
}
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
lean_del_object(v___x_619_);
v___x_823_ = lean_nat_add(v___x_763_, v_size_764_);
v___x_824_ = lean_nat_add(v___x_823_, v_size_765_);
lean_dec(v_size_765_);
v___x_825_ = lean_nat_add(v___x_823_, v_size_781_);
lean_dec(v___x_823_);
lean_inc_ref(v_l_616_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_768_);
lean_ctor_set(v___x_779_, 3, v_l_616_);
lean_ctor_set(v___x_779_, 2, v_v_615_);
lean_ctor_set(v___x_779_, 1, v_k_614_);
lean_ctor_set(v___x_779_, 0, v___x_825_);
v___x_827_ = v___x_779_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_l_616_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_l_768_);
v___x_827_ = v_reuseFailAlloc_840_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v_l_616_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_835_ = lean_ctor_get(v_l_616_, 4);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_l_616_, 3);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_l_616_, 2);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_l_616_, 1);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_616_, 0);
lean_dec(v_unused_839_);
v___x_829_ = v_l_616_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_l_616_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v_r_769_);
lean_ctor_set(v___x_829_, 3, v___x_827_);
lean_ctor_set(v___x_829_, 2, v_v_767_);
lean_ctor_set(v___x_829_, 1, v_k_766_);
lean_ctor_set(v___x_829_, 0, v___x_824_);
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_k_766_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_v_767_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_r_769_);
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
}
}
}
else
{
lean_object* v_l_847_; 
v_l_847_ = lean_ctor_get(v_impl_762_, 3);
lean_inc(v_l_847_);
if (lean_obj_tag(v_l_847_) == 0)
{
lean_object* v_r_848_; lean_object* v_k_849_; lean_object* v_v_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_873_; 
v_r_848_ = lean_ctor_get(v_impl_762_, 4);
v_k_849_ = lean_ctor_get(v_impl_762_, 1);
v_v_850_ = lean_ctor_get(v_impl_762_, 2);
v_isSharedCheck_873_ = !lean_is_exclusive(v_impl_762_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; lean_object* v_unused_875_; 
v_unused_874_ = lean_ctor_get(v_impl_762_, 3);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_impl_762_, 0);
lean_dec(v_unused_875_);
v___x_852_ = v_impl_762_;
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_r_848_);
lean_inc(v_v_850_);
lean_inc(v_k_849_);
lean_dec(v_impl_762_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_k_854_; lean_object* v_v_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_869_; 
v_k_854_ = lean_ctor_get(v_l_847_, 1);
v_v_855_ = lean_ctor_get(v_l_847_, 2);
v_isSharedCheck_869_ = !lean_is_exclusive(v_l_847_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; 
v_unused_870_ = lean_ctor_get(v_l_847_, 4);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_l_847_, 3);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_l_847_, 0);
lean_dec(v_unused_872_);
v___x_857_ = v_l_847_;
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_v_855_);
lean_inc(v_k_854_);
lean_dec(v_l_847_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_848_, 2);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 4, v_r_848_);
lean_ctor_set(v___x_857_, 3, v_r_848_);
lean_ctor_set(v___x_857_, 2, v_v_615_);
lean_ctor_set(v___x_857_, 1, v_k_614_);
lean_ctor_set(v___x_857_, 0, v___x_763_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_r_848_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_r_848_);
v___x_861_ = v_reuseFailAlloc_868_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
lean_inc(v_r_848_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 3, v_r_848_);
lean_ctor_set(v___x_852_, 0, v___x_763_);
v___x_863_ = v___x_852_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_k_849_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_v_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_r_848_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_r_848_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v___x_863_);
lean_ctor_set(v___x_619_, 3, v___x_861_);
lean_ctor_set(v___x_619_, 2, v_v_855_);
lean_ctor_set(v___x_619_, 1, v_k_854_);
lean_ctor_set(v___x_619_, 0, v___x_859_);
v___x_865_ = v___x_619_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_855_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v_r_876_; 
v_r_876_ = lean_ctor_get(v_impl_762_, 4);
lean_inc(v_r_876_);
if (lean_obj_tag(v_r_876_) == 0)
{
lean_object* v_k_877_; lean_object* v_v_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_889_; 
v_k_877_ = lean_ctor_get(v_impl_762_, 1);
v_v_878_ = lean_ctor_get(v_impl_762_, 2);
v_isSharedCheck_889_ = !lean_is_exclusive(v_impl_762_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_890_ = lean_ctor_get(v_impl_762_, 4);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_impl_762_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_impl_762_, 0);
lean_dec(v_unused_892_);
v___x_880_ = v_impl_762_;
v_isShared_881_ = v_isSharedCheck_889_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_v_878_);
lean_inc(v_k_877_);
lean_dec(v_impl_762_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_889_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_unsigned_to_nat(3u);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 4, v_l_847_);
lean_ctor_set(v___x_880_, 2, v_v_615_);
lean_ctor_set(v___x_880_, 1, v_k_614_);
lean_ctor_set(v___x_880_, 0, v___x_763_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_l_847_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_l_847_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_r_876_);
lean_ctor_set(v___x_619_, 3, v___x_884_);
lean_ctor_set(v___x_619_, 2, v_v_878_);
lean_ctor_set(v___x_619_, 1, v_k_877_);
lean_ctor_set(v___x_619_, 0, v___x_882_);
v___x_886_ = v___x_619_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_r_876_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(2u);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_impl_762_);
lean_ctor_set(v___x_619_, 3, v_r_876_);
lean_ctor_set(v___x_619_, 0, v___x_893_);
v___x_895_ = v___x_619_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_v_615_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_r_876_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_impl_762_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
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
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_k_610_);
lean_ctor_set(v___x_899_, 2, v_v_611_);
lean_ctor_set(v___x_899_, 3, v_t_612_);
lean_ctor_set(v___x_899_, 4, v_t_612_);
return v___x_899_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(lean_object* v_k_900_, lean_object* v_t_901_){
_start:
{
if (lean_obj_tag(v_t_901_) == 0)
{
lean_object* v_k_902_; lean_object* v_l_903_; lean_object* v_r_904_; uint8_t v___x_905_; 
v_k_902_ = lean_ctor_get(v_t_901_, 1);
v_l_903_ = lean_ctor_get(v_t_901_, 3);
v_r_904_ = lean_ctor_get(v_t_901_, 4);
v___x_905_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_900_, v_k_902_);
switch(v___x_905_)
{
case 0:
{
v_t_901_ = v_l_903_;
goto _start;
}
case 1:
{
uint8_t v___x_907_; 
v___x_907_ = 1;
return v___x_907_;
}
default: 
{
v_t_901_ = v_r_904_;
goto _start;
}
}
}
else
{
uint8_t v___x_909_; 
v___x_909_ = 0;
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg___boxed(lean_object* v_k_910_, lean_object* v_t_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_910_, v_t_911_);
lean_dec(v_t_911_);
lean_dec(v_k_910_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object* v___y_914_){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_box(1);
v___x_916_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v___y_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___y_914_, v___x_917_, v___x_915_);
return v___x_918_;
}
else
{
lean_dec(v___y_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(lean_object* v_00_u03b2_921_, lean_object* v_k_922_, lean_object* v_t_923_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_k_922_, v_t_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___boxed(lean_object* v_00_u03b2_925_, lean_object* v_k_926_, lean_object* v_t_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0(v_00_u03b2_925_, v_k_926_, v_t_927_);
lean_dec(v_t_927_);
lean_dec(v_k_926_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1(lean_object* v_00_u03b2_930_, lean_object* v_k_931_, lean_object* v_v_932_, lean_object* v_t_933_, lean_object* v_hl_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_k_931_, v_v_932_, v_t_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v_c_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_apply_2(v_f_936_, v_a_937_, v_c_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_941_, lean_object* v_____do__lift_942_){
_start:
{
lean_object* v_a_943_; lean_object* v___x_944_; 
v_a_943_ = lean_ctor_get(v_____do__lift_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v_____do__lift_942_);
v___x_944_ = lean_apply_2(v_toPure_941_, lean_box(0), v_a_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg(lean_object* v_inst_945_, lean_object* v_m_946_, lean_object* v_init_947_, lean_object* v_f_948_){
_start:
{
lean_object* v_toApplicative_949_; lean_object* v_toBind_950_; lean_object* v_toPure_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; 
v_toApplicative_949_ = lean_ctor_get(v_inst_945_, 0);
v_toBind_950_ = lean_ctor_get(v_inst_945_, 1);
lean_inc(v_toBind_950_);
v_toPure_951_ = lean_ctor_get(v_toApplicative_949_, 1);
lean_inc(v_toPure_951_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_952_, 0, v_f_948_);
v___x_953_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_945_, v___f_952_, v_init_947_, v_m_946_);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_954_, 0, v_toPure_951_);
v___x_955_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_953_, v___f_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1(lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v_00_u03b2_958_, lean_object* v_m_959_, lean_object* v_init_960_, lean_object* v_f_961_){
_start:
{
lean_object* v_toApplicative_962_; lean_object* v_toBind_963_; lean_object* v_toPure_964_; lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___f_967_; lean_object* v___x_968_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_957_, 0);
v_toBind_963_ = lean_ctor_get(v_inst_957_, 1);
lean_inc(v_toBind_963_);
v_toPure_964_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc(v_toPure_964_);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_965_, 0, v_f_961_);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_957_, v___f_965_, v_init_960_, v_m_959_);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_967_, 0, v_toPure_964_);
v___x_968_ = lean_apply_4(v_toBind_963_, lean_box(0), lean_box(0), v___x_966_, v___f_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad___redArg(lean_object* v_inst_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_970_, 0, lean_box(0));
lean_closure_set(v___x_970_, 1, v_inst_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarIdOfMonad(lean_object* v_m_971_, lean_object* v_inst_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_973_, 0, lean_box(0));
lean_closure_set(v___x_973_, 1, v_inst_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_insert(lean_object* v_s_974_, lean_object* v_fvarId_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_instSingletonFVarIdFVarIdSet_spec__0___redArg(v_fvarId_975_, v_s_974_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_box(0);
v___x_978_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_975_, v___x_977_, v_s_974_);
return v___x_978_;
}
else
{
lean_dec(v_fvarId_975_);
return v_s_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(lean_object* v_init_979_, lean_object* v_x_980_){
_start:
{
if (lean_obj_tag(v_x_980_) == 0)
{
lean_object* v_k_981_; lean_object* v_l_982_; lean_object* v_r_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_k_981_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_k_981_);
v_l_982_ = lean_ctor_get(v_x_980_, 3);
lean_inc(v_l_982_);
v_r_983_ = lean_ctor_get(v_x_980_, 4);
lean_inc(v_r_983_);
lean_dec_ref_known(v_x_980_, 5);
v___x_984_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_979_, v_l_982_);
v___x_985_ = l_Lean_FVarIdSet_insert(v___x_984_, v_k_981_);
v_init_979_ = v___x_985_;
v_x_980_ = v_r_983_;
goto _start;
}
else
{
return v_init_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_union(lean_object* v_vs_u2081_987_, lean_object* v_vs_u2082_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_vs_u2082_988_, v_vs_u2081_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0(lean_object* v_init_990_, lean_object* v_t_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_FVarIdSet_union_spec__0_spec__0(v_init_990_, v_t_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList(lean_object* v_l_993_){
_start:
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_995_ = l_Std_TreeSet_ofList___redArg(v_l_993_, v___f_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofList___boxed(lean_object* v_l_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_FVarIdSet_ofList(v_l_996_);
lean_dec(v_l_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray(lean_object* v_l_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; 
v___f_999_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1000_ = l_Std_TreeSet_ofArray___redArg(v_l_998_, v___f_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdSet_ofArray___boxed(lean_object* v_l_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_FVarIdSet_ofArray(v_l_1001_);
lean_dec_ref(v_l_1001_);
return v_res_1002_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_unsigned_to_nat(16u);
v___x_1005_ = lean_mk_array(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__0);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarIdHashSet(void){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionFVarIdHashSet(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1, &l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1_once, _init_l_Lean_instInhabitedFVarIdHashSet___aux__1___closed__1);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert___redArg(lean_object* v_s_1013_, lean_object* v_fvarId_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1014_, v_a_1015_, v_s_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarIdMap_insert(lean_object* v_00_u03b1_1017_, lean_object* v_s_1018_, lean_object* v_fvarId_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1019_, v_a_1020_, v_s_1018_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(1);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_instEmptyCollectionFVarIdMap___aux__1___redArg();
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___aux__1(lean_object* v_00_u03b1_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_box(1);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_box(1);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap___redArg___boxed(lean_object* v___dummy_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_instEmptyCollectionFVarIdMap___redArg();
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* v_00_u03b1_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_box(1);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg(){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_box(1);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap___redArg___boxed(lean_object* v___dummy_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_instInhabitedFVarIdMap___redArg();
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* v_00_u03b1_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(1);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId_default(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarId(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqMVarId_beq(lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_name_eq(v_x_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId_beq___boxed(lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Lean_instBEqMVarId_beq(v_x_1045_, v_x_1046_);
lean_dec(v_x_1046_);
lean_dec(v_x_1045_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableMVarId_hash(lean_object* v_x_1051_){
_start:
{
uint64_t v___x_1052_; 
v___x_1052_ = 0ULL;
if (lean_obj_tag(v_x_1051_) == 0)
{
uint64_t v___x_1053_; 
v___x_1053_ = 8934034000889494153ULL;
return v___x_1053_;
}
else
{
uint64_t v_hash_1054_; uint64_t v___x_1055_; 
v_hash_1054_ = lean_ctor_get_uint64(v_x_1051_, sizeof(void*)*2);
v___x_1055_ = lean_uint64_mix_hash(v___x_1052_, v_hash_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId_hash___boxed(lean_object* v_x_1056_){
_start:
{
uint64_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Lean_instHashableMVarId_hash(v_x_1056_);
lean_dec(v_x_1056_);
v_r_1058_ = lean_box_uint64(v_res_1057_);
return v_r_1058_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_box(1);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_instInhabitedMVarIdSet(void){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_box(1);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1(void){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(1);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_instEmptyCollectionMVarIdSet(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(1);
return v___x_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(lean_object* v_k_1066_, lean_object* v_t_1067_){
_start:
{
if (lean_obj_tag(v_t_1067_) == 0)
{
lean_object* v_k_1068_; lean_object* v_l_1069_; lean_object* v_r_1070_; uint8_t v___x_1071_; 
v_k_1068_ = lean_ctor_get(v_t_1067_, 1);
v_l_1069_ = lean_ctor_get(v_t_1067_, 3);
v_r_1070_ = lean_ctor_get(v_t_1067_, 4);
v___x_1071_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1066_, v_k_1068_);
switch(v___x_1071_)
{
case 0:
{
v_t_1067_ = v_l_1069_;
goto _start;
}
case 1:
{
uint8_t v___x_1073_; 
v___x_1073_ = 1;
return v___x_1073_;
}
default: 
{
v_t_1067_ = v_r_1070_;
goto _start;
}
}
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg___boxed(lean_object* v_k_1076_, lean_object* v_t_1077_){
_start:
{
uint8_t v_res_1078_; lean_object* v_r_1079_; 
v_res_1078_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1076_, v_t_1077_);
lean_dec(v_t_1077_);
lean_dec(v_k_1076_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(lean_object* v_k_1080_, lean_object* v_v_1081_, lean_object* v_t_1082_){
_start:
{
if (lean_obj_tag(v_t_1082_) == 0)
{
lean_object* v_size_1083_; lean_object* v_k_1084_; lean_object* v_v_1085_; lean_object* v_l_1086_; lean_object* v_r_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1367_; 
v_size_1083_ = lean_ctor_get(v_t_1082_, 0);
v_k_1084_ = lean_ctor_get(v_t_1082_, 1);
v_v_1085_ = lean_ctor_get(v_t_1082_, 2);
v_l_1086_ = lean_ctor_get(v_t_1082_, 3);
v_r_1087_ = lean_ctor_get(v_t_1082_, 4);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_t_1082_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1089_ = v_t_1082_;
v_isShared_1090_ = v_isSharedCheck_1367_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_r_1087_);
lean_inc(v_l_1086_);
lean_inc(v_v_1085_);
lean_inc(v_k_1084_);
lean_inc(v_size_1083_);
lean_dec(v_t_1082_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1367_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1080_, v_k_1084_);
switch(v___x_1091_)
{
case 0:
{
lean_object* v_impl_1092_; lean_object* v___x_1093_; 
lean_dec(v_size_1083_);
v_impl_1092_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1080_, v_v_1081_, v_l_1086_);
v___x_1093_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1087_) == 0)
{
lean_object* v_size_1094_; lean_object* v_size_1095_; lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_l_1098_; lean_object* v_r_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_size_1094_ = lean_ctor_get(v_r_1087_, 0);
v_size_1095_ = lean_ctor_get(v_impl_1092_, 0);
v_k_1096_ = lean_ctor_get(v_impl_1092_, 1);
v_v_1097_ = lean_ctor_get(v_impl_1092_, 2);
v_l_1098_ = lean_ctor_get(v_impl_1092_, 3);
v_r_1099_ = lean_ctor_get(v_impl_1092_, 4);
lean_inc(v_r_1099_);
v___x_1100_ = lean_unsigned_to_nat(3u);
v___x_1101_ = lean_nat_mul(v___x_1100_, v_size_1094_);
v___x_1102_ = lean_nat_dec_lt(v___x_1101_, v_size_1095_);
lean_dec(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v_r_1099_);
v___x_1103_ = lean_nat_add(v___x_1093_, v_size_1095_);
v___x_1104_ = lean_nat_add(v___x_1103_, v_size_1094_);
lean_dec(v___x_1103_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 3, v_impl_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1104_);
v___x_1106_ = v___x_1089_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_r_1087_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1173_; 
lean_inc(v_l_1098_);
lean_inc(v_v_1097_);
lean_inc(v_k_1096_);
lean_inc(v_size_1095_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1174_ = lean_ctor_get(v_impl_1092_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1092_, 2);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_impl_1092_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1178_);
v___x_1109_ = v_impl_1092_;
v_isShared_1110_ = v_isSharedCheck_1173_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_impl_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1173_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_size_1111_; lean_object* v_size_1112_; lean_object* v_k_1113_; lean_object* v_v_1114_; lean_object* v_l_1115_; lean_object* v_r_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_size_1111_ = lean_ctor_get(v_l_1098_, 0);
v_size_1112_ = lean_ctor_get(v_r_1099_, 0);
v_k_1113_ = lean_ctor_get(v_r_1099_, 1);
v_v_1114_ = lean_ctor_get(v_r_1099_, 2);
v_l_1115_ = lean_ctor_get(v_r_1099_, 3);
v_r_1116_ = lean_ctor_get(v_r_1099_, 4);
v___x_1117_ = lean_unsigned_to_nat(2u);
v___x_1118_ = lean_nat_mul(v___x_1117_, v_size_1111_);
v___x_1119_ = lean_nat_dec_lt(v_size_1112_, v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1148_; 
lean_inc(v_r_1116_);
lean_inc(v_l_1115_);
lean_inc(v_v_1114_);
lean_inc(v_k_1113_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_r_1099_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; lean_object* v_unused_1153_; 
v_unused_1149_ = lean_ctor_get(v_r_1099_, 4);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1099_, 3);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1099_, 2);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_1099_, 1);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_r_1099_, 0);
lean_dec(v_unused_1153_);
v___x_1121_ = v_r_1099_;
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v_r_1099_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1148_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___x_1136_; lean_object* v___y_1138_; 
v___x_1123_ = lean_nat_add(v___x_1093_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1124_ = lean_nat_add(v___x_1123_, v_size_1094_);
lean_dec(v___x_1123_);
v___x_1136_ = lean_nat_add(v___x_1093_, v_size_1111_);
if (lean_obj_tag(v_l_1115_) == 0)
{
lean_object* v_size_1146_; 
v_size_1146_ = lean_ctor_get(v_l_1115_, 0);
lean_inc(v_size_1146_);
v___y_1138_ = v_size_1146_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___y_1138_ = v___x_1147_;
goto v___jp_1137_;
}
v___jp_1125_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_nat_add(v___y_1126_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec(v___y_1126_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 4, v_r_1087_);
lean_ctor_set(v___x_1121_, 3, v_r_1116_);
lean_ctor_set(v___x_1121_, 2, v_v_1085_);
lean_ctor_set(v___x_1121_, 1, v_k_1084_);
lean_ctor_set(v___x_1121_, 0, v___x_1129_);
v___x_1131_ = v___x_1121_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_r_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_r_1087_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v___x_1131_);
lean_ctor_set(v___x_1109_, 3, v___y_1127_);
lean_ctor_set(v___x_1109_, 2, v_v_1114_);
lean_ctor_set(v___x_1109_, 1, v_k_1113_);
lean_ctor_set(v___x_1109_, 0, v___x_1124_);
v___x_1133_ = v___x_1109_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_k_1113_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_v_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v___y_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_nat_add(v___x_1136_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec(v___x_1136_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1115_);
lean_ctor_set(v___x_1089_, 3, v_l_1098_);
lean_ctor_set(v___x_1089_, 2, v_v_1097_);
lean_ctor_set(v___x_1089_, 1, v_k_1096_);
lean_ctor_set(v___x_1089_, 0, v___x_1139_);
v___x_1141_ = v___x_1089_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_l_1115_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_nat_add(v___x_1093_, v_size_1094_);
if (lean_obj_tag(v_r_1116_) == 0)
{
lean_object* v_size_1143_; 
v_size_1143_ = lean_ctor_get(v_r_1116_, 0);
lean_inc(v_size_1143_);
v___y_1126_ = v___x_1142_;
v___y_1127_ = v___x_1141_;
v___y_1128_ = v_size_1143_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___y_1126_ = v___x_1142_;
v___y_1127_ = v___x_1141_;
v___y_1128_ = v___x_1144_;
goto v___jp_1125_;
}
}
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_del_object(v___x_1089_);
v___x_1154_ = lean_nat_add(v___x_1093_, v_size_1095_);
lean_dec(v_size_1095_);
v___x_1155_ = lean_nat_add(v___x_1154_, v_size_1094_);
lean_dec(v___x_1154_);
v___x_1156_ = lean_nat_add(v___x_1093_, v_size_1094_);
v___x_1157_ = lean_nat_add(v___x_1156_, v_size_1112_);
lean_dec(v___x_1156_);
lean_inc_ref(v_r_1087_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v_r_1087_);
lean_ctor_set(v___x_1109_, 3, v_r_1099_);
lean_ctor_set(v___x_1109_, 2, v_v_1085_);
lean_ctor_set(v___x_1109_, 1, v_k_1084_);
lean_ctor_set(v___x_1109_, 0, v___x_1157_);
v___x_1159_ = v___x_1109_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_r_1099_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_r_1087_);
v___x_1159_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v_r_1087_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1167_ = lean_ctor_get(v_r_1087_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_r_1087_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_r_1087_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_r_1087_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_r_1087_, 0);
lean_dec(v_unused_1171_);
v___x_1161_ = v_r_1087_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_r_1087_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 4, v___x_1159_);
lean_ctor_set(v___x_1161_, 3, v_l_1098_);
lean_ctor_set(v___x_1161_, 2, v_v_1097_);
lean_ctor_set(v___x_1161_, 1, v_k_1096_);
lean_ctor_set(v___x_1161_, 0, v___x_1155_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_l_1098_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___x_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1179_; 
v_l_1179_ = lean_ctor_get(v_impl_1092_, 3);
if (lean_obj_tag(v_l_1179_) == 0)
{
lean_object* v_r_1180_; lean_object* v_k_1181_; lean_object* v_v_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1193_; 
lean_inc_ref(v_l_1179_);
v_r_1180_ = lean_ctor_get(v_impl_1092_, 4);
v_k_1181_ = lean_ctor_get(v_impl_1092_, 1);
v_v_1182_ = lean_ctor_get(v_impl_1092_, 2);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1194_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1195_);
v___x_1184_ = v_impl_1092_;
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_r_1180_);
lean_inc(v_v_1182_);
lean_inc(v_k_1181_);
lean_dec(v_impl_1092_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 3, v_r_1180_);
lean_ctor_set(v___x_1184_, 2, v_v_1085_);
lean_ctor_set(v___x_1184_, 1, v_k_1084_);
lean_ctor_set(v___x_1184_, 0, v___x_1093_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_r_1180_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1188_);
lean_ctor_set(v___x_1089_, 3, v_l_1179_);
lean_ctor_set(v___x_1089_, 2, v_v_1182_);
lean_ctor_set(v___x_1089_, 1, v_k_1181_);
lean_ctor_set(v___x_1089_, 0, v___x_1186_);
v___x_1190_ = v___x_1089_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1182_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_r_1196_; 
v_r_1196_ = lean_ctor_get(v_impl_1092_, 4);
lean_inc(v_r_1196_);
if (lean_obj_tag(v_r_1196_) == 0)
{
lean_object* v_k_1197_; lean_object* v_v_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1221_; 
lean_inc(v_l_1179_);
v_k_1197_ = lean_ctor_get(v_impl_1092_, 1);
v_v_1198_ = lean_ctor_get(v_impl_1092_, 2);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_impl_1092_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1222_ = lean_ctor_get(v_impl_1092_, 4);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_impl_1092_, 3);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_impl_1092_, 0);
lean_dec(v_unused_1224_);
v___x_1200_ = v_impl_1092_;
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_v_1198_);
lean_inc(v_k_1197_);
lean_dec(v_impl_1092_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1221_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_k_1202_; lean_object* v_v_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1217_; 
v_k_1202_ = lean_ctor_get(v_r_1196_, 1);
v_v_1203_ = lean_ctor_get(v_r_1196_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_r_1196_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; 
v_unused_1218_ = lean_ctor_get(v_r_1196_, 4);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_r_1196_, 3);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_r_1196_, 0);
lean_dec(v_unused_1220_);
v___x_1205_ = v_r_1196_;
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_v_1203_);
lean_inc(v_k_1202_);
lean_dec(v_r_1196_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(3u);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v_l_1179_);
lean_ctor_set(v___x_1205_, 3, v_l_1179_);
lean_ctor_set(v___x_1205_, 2, v_v_1198_);
lean_ctor_set(v___x_1205_, 1, v_k_1197_);
lean_ctor_set(v___x_1205_, 0, v___x_1093_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_l_1179_);
v___x_1209_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 4, v_l_1179_);
lean_ctor_set(v___x_1200_, 2, v_v_1085_);
lean_ctor_set(v___x_1200_, 1, v_k_1084_);
lean_ctor_set(v___x_1200_, 0, v___x_1093_);
v___x_1211_ = v___x_1200_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_l_1179_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_l_1179_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1211_);
lean_ctor_set(v___x_1089_, 3, v___x_1209_);
lean_ctor_set(v___x_1089_, 2, v_v_1203_);
lean_ctor_set(v___x_1089_, 1, v_k_1202_);
lean_ctor_set(v___x_1089_, 0, v___x_1207_);
v___x_1213_ = v___x_1089_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1202_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1203_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(2u);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_r_1196_);
lean_ctor_set(v___x_1089_, 3, v_impl_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1225_);
v___x_1227_ = v___x_1089_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_impl_1092_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1196_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1230_; 
lean_dec(v_v_1085_);
lean_dec(v_k_1084_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 2, v_v_1081_);
lean_ctor_set(v___x_1089_, 1, v_k_1080_);
v___x_1230_ = v___x_1089_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_size_1083_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1080_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1081_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_r_1087_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
default: 
{
lean_object* v_impl_1232_; lean_object* v___x_1233_; 
lean_dec(v_size_1083_);
v_impl_1232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1080_, v_v_1081_, v_r_1087_);
v___x_1233_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1086_) == 0)
{
lean_object* v_size_1234_; lean_object* v_size_1235_; lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v_l_1238_; lean_object* v_r_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_size_1234_ = lean_ctor_get(v_l_1086_, 0);
v_size_1235_ = lean_ctor_get(v_impl_1232_, 0);
v_k_1236_ = lean_ctor_get(v_impl_1232_, 1);
v_v_1237_ = lean_ctor_get(v_impl_1232_, 2);
v_l_1238_ = lean_ctor_get(v_impl_1232_, 3);
lean_inc(v_l_1238_);
v_r_1239_ = lean_ctor_get(v_impl_1232_, 4);
v___x_1240_ = lean_unsigned_to_nat(3u);
v___x_1241_ = lean_nat_mul(v___x_1240_, v_size_1234_);
v___x_1242_ = lean_nat_dec_lt(v___x_1241_, v_size_1235_);
lean_dec(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
lean_dec(v_l_1238_);
v___x_1243_ = lean_nat_add(v___x_1233_, v_size_1234_);
v___x_1244_ = lean_nat_add(v___x_1243_, v_size_1235_);
lean_dec(v___x_1243_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_impl_1232_);
lean_ctor_set(v___x_1089_, 0, v___x_1244_);
v___x_1246_ = v___x_1089_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_impl_1232_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
else
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1311_; 
lean_inc(v_r_1239_);
lean_inc(v_v_1237_);
lean_inc(v_k_1236_);
lean_inc(v_size_1235_);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_impl_1232_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1312_ = lean_ctor_get(v_impl_1232_, 4);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_impl_1232_, 3);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_impl_1232_, 2);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_impl_1232_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_impl_1232_, 0);
lean_dec(v_unused_1316_);
v___x_1249_ = v_impl_1232_;
v_isShared_1250_ = v_isSharedCheck_1311_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v_impl_1232_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1311_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_size_1251_; lean_object* v_k_1252_; lean_object* v_v_1253_; lean_object* v_l_1254_; lean_object* v_r_1255_; lean_object* v_size_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_size_1251_ = lean_ctor_get(v_l_1238_, 0);
v_k_1252_ = lean_ctor_get(v_l_1238_, 1);
v_v_1253_ = lean_ctor_get(v_l_1238_, 2);
v_l_1254_ = lean_ctor_get(v_l_1238_, 3);
v_r_1255_ = lean_ctor_get(v_l_1238_, 4);
v_size_1256_ = lean_ctor_get(v_r_1239_, 0);
v___x_1257_ = lean_unsigned_to_nat(2u);
v___x_1258_ = lean_nat_mul(v___x_1257_, v_size_1256_);
v___x_1259_ = lean_nat_dec_lt(v_size_1251_, v___x_1258_);
lean_dec(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1287_; 
lean_inc(v_r_1255_);
lean_inc(v_l_1254_);
lean_inc(v_v_1253_);
lean_inc(v_k_1252_);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_l_1238_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; 
v_unused_1288_ = lean_ctor_get(v_l_1238_, 4);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v_l_1238_, 3);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v_l_1238_, 2);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_l_1238_, 1);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_l_1238_, 0);
lean_dec(v_unused_1292_);
v___x_1261_ = v_l_1238_;
v_isShared_1262_ = v_isSharedCheck_1287_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v_l_1238_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1287_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1277_; 
v___x_1263_ = lean_nat_add(v___x_1233_, v_size_1234_);
v___x_1264_ = lean_nat_add(v___x_1263_, v_size_1235_);
lean_dec(v_size_1235_);
if (lean_obj_tag(v_l_1254_) == 0)
{
lean_object* v_size_1285_; 
v_size_1285_ = lean_ctor_get(v_l_1254_, 0);
lean_inc(v_size_1285_);
v___y_1277_ = v_size_1285_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___y_1277_ = v___x_1286_;
goto v___jp_1276_;
}
v___jp_1265_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_nat_add(v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v_r_1239_);
lean_ctor_set(v___x_1261_, 3, v_r_1255_);
lean_ctor_set(v___x_1261_, 2, v_v_1237_);
lean_ctor_set(v___x_1261_, 1, v_k_1236_);
lean_ctor_set(v___x_1261_, 0, v___x_1269_);
v___x_1271_ = v___x_1261_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_k_1236_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_v_1237_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_r_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_r_1239_);
v___x_1271_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 4, v___x_1271_);
lean_ctor_set(v___x_1249_, 3, v___y_1266_);
lean_ctor_set(v___x_1249_, 2, v_v_1253_);
lean_ctor_set(v___x_1249_, 1, v_k_1252_);
lean_ctor_set(v___x_1249_, 0, v___x_1264_);
v___x_1273_ = v___x_1249_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1252_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1253_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___y_1266_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_nat_add(v___x_1263_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec(v___x_1263_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1254_);
lean_ctor_set(v___x_1089_, 0, v___x_1278_);
v___x_1280_ = v___x_1089_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_l_1254_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_nat_add(v___x_1233_, v_size_1256_);
if (lean_obj_tag(v_r_1255_) == 0)
{
lean_object* v_size_1282_; 
v_size_1282_ = lean_ctor_get(v_r_1255_, 0);
lean_inc(v_size_1282_);
v___y_1266_ = v___x_1280_;
v___y_1267_ = v___x_1281_;
v___y_1268_ = v_size_1282_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_unsigned_to_nat(0u);
v___y_1266_ = v___x_1280_;
v___y_1267_ = v___x_1281_;
v___y_1268_ = v___x_1283_;
goto v___jp_1265_;
}
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_del_object(v___x_1089_);
v___x_1293_ = lean_nat_add(v___x_1233_, v_size_1234_);
v___x_1294_ = lean_nat_add(v___x_1293_, v_size_1235_);
lean_dec(v_size_1235_);
v___x_1295_ = lean_nat_add(v___x_1293_, v_size_1251_);
lean_dec(v___x_1293_);
lean_inc_ref(v_l_1086_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 4, v_l_1238_);
lean_ctor_set(v___x_1249_, 3, v_l_1086_);
lean_ctor_set(v___x_1249_, 2, v_v_1085_);
lean_ctor_set(v___x_1249_, 1, v_k_1084_);
lean_ctor_set(v___x_1249_, 0, v___x_1295_);
v___x_1297_ = v___x_1249_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_l_1086_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_l_1238_);
v___x_1297_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_isSharedCheck_1304_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; lean_object* v_unused_1309_; 
v_unused_1305_ = lean_ctor_get(v_l_1086_, 4);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_l_1086_, 3);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_l_1086_, 2);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_l_1086_, 1);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_l_1086_, 0);
lean_dec(v_unused_1309_);
v___x_1299_ = v_l_1086_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_l_1086_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v_r_1239_);
lean_ctor_set(v___x_1299_, 3, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v_v_1237_);
lean_ctor_set(v___x_1299_, 1, v_k_1236_);
lean_ctor_set(v___x_1299_, 0, v___x_1294_);
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1236_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1237_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_r_1239_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1317_; 
v_l_1317_ = lean_ctor_get(v_impl_1232_, 3);
lean_inc(v_l_1317_);
if (lean_obj_tag(v_l_1317_) == 0)
{
lean_object* v_r_1318_; lean_object* v_k_1319_; lean_object* v_v_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1343_; 
v_r_1318_ = lean_ctor_get(v_impl_1232_, 4);
v_k_1319_ = lean_ctor_get(v_impl_1232_, 1);
v_v_1320_ = lean_ctor_get(v_impl_1232_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_impl_1232_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; lean_object* v_unused_1345_; 
v_unused_1344_ = lean_ctor_get(v_impl_1232_, 3);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_impl_1232_, 0);
lean_dec(v_unused_1345_);
v___x_1322_ = v_impl_1232_;
v_isShared_1323_ = v_isSharedCheck_1343_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_r_1318_);
lean_inc(v_v_1320_);
lean_inc(v_k_1319_);
lean_dec(v_impl_1232_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1343_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1339_; 
v_k_1324_ = lean_ctor_get(v_l_1317_, 1);
v_v_1325_ = lean_ctor_get(v_l_1317_, 2);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_l_1317_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1340_ = lean_ctor_get(v_l_1317_, 4);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_l_1317_, 3);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_l_1317_, 0);
lean_dec(v_unused_1342_);
v___x_1327_ = v_l_1317_;
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_v_1325_);
lean_inc(v_k_1324_);
lean_dec(v_l_1317_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1318_, 2);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v_r_1318_);
lean_ctor_set(v___x_1327_, 3, v_r_1318_);
lean_ctor_set(v___x_1327_, 2, v_v_1085_);
lean_ctor_set(v___x_1327_, 1, v_k_1084_);
lean_ctor_set(v___x_1327_, 0, v___x_1233_);
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_r_1318_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_r_1318_);
v___x_1331_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
lean_inc(v_r_1318_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 3, v_r_1318_);
lean_ctor_set(v___x_1322_, 0, v___x_1233_);
v___x_1333_ = v___x_1322_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1319_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1320_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_r_1318_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_r_1318_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v___x_1333_);
lean_ctor_set(v___x_1089_, 3, v___x_1331_);
lean_ctor_set(v___x_1089_, 2, v_v_1325_);
lean_ctor_set(v___x_1089_, 1, v_k_1324_);
lean_ctor_set(v___x_1089_, 0, v___x_1329_);
v___x_1335_ = v___x_1089_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1325_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
else
{
lean_object* v_r_1346_; 
v_r_1346_ = lean_ctor_get(v_impl_1232_, 4);
lean_inc(v_r_1346_);
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_k_1347_; lean_object* v_v_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_k_1347_ = lean_ctor_get(v_impl_1232_, 1);
v_v_1348_ = lean_ctor_get(v_impl_1232_, 2);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_impl_1232_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; 
v_unused_1360_ = lean_ctor_get(v_impl_1232_, 4);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_impl_1232_, 3);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_impl_1232_, 0);
lean_dec(v_unused_1362_);
v___x_1350_ = v_impl_1232_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_v_1348_);
lean_inc(v_k_1347_);
lean_dec(v_impl_1232_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_unsigned_to_nat(3u);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 4, v_l_1317_);
lean_ctor_set(v___x_1350_, 2, v_v_1085_);
lean_ctor_set(v___x_1350_, 1, v_k_1084_);
lean_ctor_set(v___x_1350_, 0, v___x_1233_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_l_1317_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_l_1317_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_r_1346_);
lean_ctor_set(v___x_1089_, 3, v___x_1354_);
lean_ctor_set(v___x_1089_, 2, v_v_1348_);
lean_ctor_set(v___x_1089_, 1, v_k_1347_);
lean_ctor_set(v___x_1089_, 0, v___x_1352_);
v___x_1356_ = v___x_1089_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1347_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1348_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_r_1346_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(2u);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_impl_1232_);
lean_ctor_set(v___x_1089_, 3, v_r_1346_);
lean_ctor_set(v___x_1089_, 0, v___x_1363_);
v___x_1365_ = v___x_1089_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1084_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1085_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_r_1346_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_impl_1232_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
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
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(1u);
v___x_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v_k_1080_);
lean_ctor_set(v___x_1369_, 2, v_v_1081_);
lean_ctor_set(v___x_1369_, 3, v_t_1082_);
lean_ctor_set(v___x_1369_, 4, v_t_1082_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_insert(lean_object* v_s_1370_, lean_object* v_mvarId_1371_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_mvarId_1371_, v_s_1370_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1371_, v___x_1373_, v_s_1370_);
return v___x_1374_;
}
else
{
lean_dec(v_mvarId_1371_);
return v_s_1370_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(lean_object* v_00_u03b2_1375_, lean_object* v_k_1376_, lean_object* v_t_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___redArg(v_k_1376_, v_t_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0___boxed(lean_object* v_00_u03b2_1379_, lean_object* v_k_1380_, lean_object* v_t_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_MVarIdSet_insert_spec__0(v_00_u03b2_1379_, v_k_1380_, v_t_1381_);
lean_dec(v_t_1381_);
lean_dec(v_k_1380_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1(lean_object* v_00_u03b2_1384_, lean_object* v_k_1385_, lean_object* v_v_1386_, lean_object* v_t_1387_, lean_object* v_hl_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_k_1385_, v_v_1386_, v_t_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList(lean_object* v_l_1390_){
_start:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; 
v___f_1391_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1392_ = l_Std_TreeSet_ofList___redArg(v_l_1390_, v___f_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofList___boxed(lean_object* v_l_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_MVarIdSet_ofList(v_l_1393_);
lean_dec(v_l_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray(lean_object* v_l_1395_){
_start:
{
lean_object* v___f_1396_; lean_object* v___x_1397_; 
v___f_1396_ = ((lean_object*)(l_Lean_instSingletonFVarIdFVarIdSet___aux__1___closed__0));
v___x_1397_ = l_Std_TreeSet_ofArray___redArg(v_l_1395_, v___f_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdSet_ofArray___boxed(lean_object* v_l_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_MVarIdSet_ofArray(v_l_1398_);
lean_dec_ref(v_l_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1400_, lean_object* v_m_1401_, lean_object* v_init_1402_, lean_object* v_f_1403_){
_start:
{
lean_object* v_toApplicative_1404_; lean_object* v_toBind_1405_; lean_object* v_toPure_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; 
v_toApplicative_1404_ = lean_ctor_get(v_inst_1400_, 0);
v_toBind_1405_ = lean_ctor_get(v_inst_1400_, 1);
lean_inc(v_toBind_1405_);
v_toPure_1406_ = lean_ctor_get(v_toApplicative_1404_, 1);
lean_inc(v_toPure_1406_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1407_, 0, v_f_1403_);
v___x_1408_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1400_, v___f_1407_, v_init_1402_, v_m_1401_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1409_, 0, v_toPure_1406_);
v___x_1410_ = lean_apply_4(v_toBind_1405_, lean_box(0), lean_box(0), v___x_1408_, v___f_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1(lean_object* v_m_1411_, lean_object* v_inst_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_m_1414_, lean_object* v_init_1415_, lean_object* v_f_1416_){
_start:
{
lean_object* v_toApplicative_1417_; lean_object* v_toBind_1418_; lean_object* v_toPure_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; 
v_toApplicative_1417_ = lean_ctor_get(v_inst_1412_, 0);
v_toBind_1418_ = lean_ctor_get(v_inst_1412_, 1);
lean_inc(v_toBind_1418_);
v_toPure_1419_ = lean_ctor_get(v_toApplicative_1417_, 1);
lean_inc(v_toPure_1419_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1420_, 0, v_f_1416_);
v___x_1421_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1412_, v___f_1420_, v_init_1415_, v_m_1414_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1422_, 0, v_toPure_1419_);
v___x_1423_ = lean_apply_4(v_toBind_1418_, lean_box(0), lean_box(0), v___x_1421_, v___f_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad___redArg(lean_object* v_inst_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1425_, 0, lean_box(0));
lean_closure_set(v___x_1425_, 1, v_inst_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarIdOfMonad(lean_object* v_m_1426_, lean_object* v_inst_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdSetMVarIdOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_1428_, 0, lean_box(0));
lean_closure_set(v___x_1428_, 1, v_inst_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert___redArg(lean_object* v_s_1429_, lean_object* v_mvarId_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1430_, v_a_1431_, v_s_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarIdMap_insert(lean_object* v_00_u03b1_1433_, lean_object* v_s_1434_, lean_object* v_mvarId_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_mvarId_1435_, v_a_1436_, v_s_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg(){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_box(1);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg___boxed(lean_object* v___dummy_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_instEmptyCollectionMVarIdMap___aux__1___redArg();
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___aux__1(lean_object* v_00_u03b1_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_box(1);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_box(1);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap___redArg___boxed(lean_object* v___dummy_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_instEmptyCollectionMVarIdMap___redArg();
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* v_00_u03b1_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_box(1);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0(lean_object* v_f_1450_, lean_object* v_a_1451_, lean_object* v_b_1452_, lean_object* v_c_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1451_);
lean_ctor_set(v___x_1454_, 1, v_b_1452_);
v___x_1455_ = lean_apply_2(v_f_1450_, v___x_1454_, v_c_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg(lean_object* v_inst_1456_, lean_object* v_m_1457_, lean_object* v_init_1458_, lean_object* v_f_1459_){
_start:
{
lean_object* v_toApplicative_1460_; lean_object* v_toBind_1461_; lean_object* v_toPure_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; 
v_toApplicative_1460_ = lean_ctor_get(v_inst_1456_, 0);
v_toBind_1461_ = lean_ctor_get(v_inst_1456_, 1);
lean_inc(v_toBind_1461_);
v_toPure_1462_ = lean_ctor_get(v_toApplicative_1460_, 1);
lean_inc(v_toPure_1462_);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1463_, 0, v_f_1459_);
v___x_1464_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1456_, v___f_1463_, v_init_1458_, v_m_1457_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1465_, 0, v_toPure_1462_);
v___x_1466_ = lean_apply_4(v_toBind_1461_, lean_box(0), lean_box(0), v___x_1464_, v___f_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1(lean_object* v_m_1467_, lean_object* v_00_u03b1_1468_, lean_object* v_inst_1469_, lean_object* v_00_u03b2_1470_, lean_object* v_m_1471_, lean_object* v_init_1472_, lean_object* v_f_1473_){
_start:
{
lean_object* v_toApplicative_1474_; lean_object* v_toBind_1475_; lean_object* v_toPure_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; 
v_toApplicative_1474_ = lean_ctor_get(v_inst_1469_, 0);
v_toBind_1475_ = lean_ctor_get(v_inst_1469_, 1);
lean_inc(v_toBind_1475_);
v_toPure_1476_ = lean_ctor_get(v_toApplicative_1474_, 1);
lean_inc(v_toPure_1476_);
v___f_1477_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1477_, 0, v_f_1473_);
v___x_1478_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_1469_, v___f_1477_, v_init_1472_, v_m_1471_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_instForInFVarIdSetFVarIdOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1479_, 0, v_toPure_1476_);
v___x_1480_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v___x_1478_, v___f_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad___redArg(lean_object* v_inst_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1482_, 0, lean_box(0));
lean_closure_set(v___x_1482_, 1, lean_box(0));
lean_closure_set(v___x_1482_, 2, v_inst_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarIdOfMonad(lean_object* v_m_1483_, lean_object* v_00_u03b1_1484_, lean_object* v_inst_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_instForInMVarIdMapProdMVarIdOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_1486_, 0, lean_box(0));
lean_closure_set(v___x_1486_, 1, lean_box(0));
lean_closure_set(v___x_1486_, 2, v_inst_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg(){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_box(1);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap___redArg___boxed(lean_object* v___dummy_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_instInhabitedMVarIdMap___redArg();
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* v_00_u03b1_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_box(1);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl(lean_object* v_x_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_obj_tag_nat(v_x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorIdx___impl___boxed(lean_object* v_x_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Expr_ctorIdx___impl(v_x_1495_);
lean_dec_ref(v_x_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___redArg(lean_object* v_t_1497_, lean_object* v_k_1498_){
_start:
{
switch(lean_obj_tag(v_t_1497_))
{
case 4:
{
lean_object* v_declName_1499_; lean_object* v_us_1500_; lean_object* v___x_1501_; 
v_declName_1499_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_declName_1499_);
v_us_1500_ = lean_ctor_get(v_t_1497_, 1);
lean_inc(v_us_1500_);
lean_dec_ref_known(v_t_1497_, 2);
v___x_1501_ = lean_apply_2(v_k_1498_, v_declName_1499_, v_us_1500_);
return v___x_1501_;
}
case 5:
{
lean_object* v_fn_1502_; lean_object* v_arg_1503_; lean_object* v___x_1504_; 
v_fn_1502_ = lean_ctor_get(v_t_1497_, 0);
lean_inc_ref(v_fn_1502_);
v_arg_1503_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_arg_1503_);
lean_dec_ref_known(v_t_1497_, 2);
v___x_1504_ = lean_apply_2(v_k_1498_, v_fn_1502_, v_arg_1503_);
return v___x_1504_;
}
case 6:
{
lean_object* v_binderName_1505_; lean_object* v_binderType_1506_; lean_object* v_body_1507_; uint8_t v_binderInfo_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_binderName_1505_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_binderName_1505_);
v_binderType_1506_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_binderType_1506_);
v_body_1507_ = lean_ctor_get(v_t_1497_, 2);
lean_inc_ref(v_body_1507_);
v_binderInfo_1508_ = lean_ctor_get_uint8(v_t_1497_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1497_, 3);
v___x_1509_ = lean_box(v_binderInfo_1508_);
v___x_1510_ = lean_apply_4(v_k_1498_, v_binderName_1505_, v_binderType_1506_, v_body_1507_, v___x_1509_);
return v___x_1510_;
}
case 7:
{
lean_object* v_binderName_1511_; lean_object* v_binderType_1512_; lean_object* v_body_1513_; uint8_t v_binderInfo_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_binderName_1511_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_binderName_1511_);
v_binderType_1512_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_binderType_1512_);
v_body_1513_ = lean_ctor_get(v_t_1497_, 2);
lean_inc_ref(v_body_1513_);
v_binderInfo_1514_ = lean_ctor_get_uint8(v_t_1497_, sizeof(void*)*3);
lean_dec_ref_known(v_t_1497_, 3);
v___x_1515_ = lean_box(v_binderInfo_1514_);
v___x_1516_ = lean_apply_4(v_k_1498_, v_binderName_1511_, v_binderType_1512_, v_body_1513_, v___x_1515_);
return v___x_1516_;
}
case 8:
{
lean_object* v_declName_1517_; lean_object* v_type_1518_; lean_object* v_value_1519_; lean_object* v_body_1520_; uint8_t v_nondep_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_declName_1517_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_declName_1517_);
v_type_1518_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_type_1518_);
v_value_1519_ = lean_ctor_get(v_t_1497_, 2);
lean_inc_ref(v_value_1519_);
v_body_1520_ = lean_ctor_get(v_t_1497_, 3);
lean_inc_ref(v_body_1520_);
v_nondep_1521_ = lean_ctor_get_uint8(v_t_1497_, sizeof(void*)*4);
lean_dec_ref_known(v_t_1497_, 4);
v___x_1522_ = lean_box(v_nondep_1521_);
v___x_1523_ = lean_apply_5(v_k_1498_, v_declName_1517_, v_type_1518_, v_value_1519_, v_body_1520_, v___x_1522_);
return v___x_1523_;
}
case 9:
{
lean_object* v_a_1524_; lean_object* v___x_1525_; 
v_a_1524_ = lean_ctor_get(v_t_1497_, 0);
lean_inc_ref(v_a_1524_);
lean_dec_ref_known(v_t_1497_, 1);
v___x_1525_ = lean_apply_1(v_k_1498_, v_a_1524_);
return v___x_1525_;
}
case 10:
{
lean_object* v_data_1526_; lean_object* v_expr_1527_; lean_object* v___x_1528_; 
v_data_1526_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_data_1526_);
v_expr_1527_ = lean_ctor_get(v_t_1497_, 1);
lean_inc_ref(v_expr_1527_);
lean_dec_ref_known(v_t_1497_, 2);
v___x_1528_ = lean_apply_2(v_k_1498_, v_data_1526_, v_expr_1527_);
return v___x_1528_;
}
case 11:
{
lean_object* v_typeName_1529_; lean_object* v_idx_1530_; lean_object* v_struct_1531_; lean_object* v___x_1532_; 
v_typeName_1529_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_typeName_1529_);
v_idx_1530_ = lean_ctor_get(v_t_1497_, 1);
lean_inc(v_idx_1530_);
v_struct_1531_ = lean_ctor_get(v_t_1497_, 2);
lean_inc_ref(v_struct_1531_);
lean_dec_ref_known(v_t_1497_, 3);
v___x_1532_ = lean_apply_3(v_k_1498_, v_typeName_1529_, v_idx_1530_, v_struct_1531_);
return v___x_1532_;
}
default: 
{
lean_object* v_deBruijnIndex_1533_; lean_object* v___x_1534_; 
v_deBruijnIndex_1533_ = lean_ctor_get(v_t_1497_, 0);
lean_inc(v_deBruijnIndex_1533_);
lean_dec_ref(v_t_1497_);
v___x_1534_ = lean_apply_1(v_k_1498_, v_deBruijnIndex_1533_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim(lean_object* v_motive_1535_, lean_object* v_ctorIdx_1536_, lean_object* v_t_1537_, lean_object* v_h_1538_, lean_object* v_k_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Expr_ctorElim___redArg(v_t_1537_, v_k_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorElim___boxed(lean_object* v_motive_1541_, lean_object* v_ctorIdx_1542_, lean_object* v_t_1543_, lean_object* v_h_1544_, lean_object* v_k_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Expr_ctorElim(v_motive_1541_, v_ctorIdx_1542_, v_t_1543_, v_h_1544_, v_k_1545_);
lean_dec(v_ctorIdx_1542_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim___redArg(lean_object* v_t_1547_, lean_object* v_bvar_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Expr_ctorElim___redArg(v_t_1547_, v_bvar_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar_elim(lean_object* v_motive_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_bvar_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Expr_ctorElim___redArg(v_t_1551_, v_bvar_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim___redArg(lean_object* v_t_1555_, lean_object* v_fvar_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Expr_ctorElim___redArg(v_t_1555_, v_fvar_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar_elim(lean_object* v_motive_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_fvar_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Expr_ctorElim___redArg(v_t_1559_, v_fvar_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim___redArg(lean_object* v_t_1563_, lean_object* v_mvar_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Expr_ctorElim___redArg(v_t_1563_, v_mvar_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_mvar_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Expr_ctorElim___redArg(v_t_1567_, v_mvar_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim___redArg(lean_object* v_t_1571_, lean_object* v_sort_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Expr_ctorElim___redArg(v_t_1571_, v_sort_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_sort_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Expr_ctorElim___redArg(v_t_1575_, v_sort_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim___redArg(lean_object* v_t_1579_, lean_object* v_const_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Expr_ctorElim___redArg(v_t_1579_, v_const_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_const_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Expr_ctorElim___redArg(v_t_1583_, v_const_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim___redArg(lean_object* v_t_1587_, lean_object* v_app_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Expr_ctorElim___redArg(v_t_1587_, v_app_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app_elim(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_app_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Expr_ctorElim___redArg(v_t_1591_, v_app_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim___redArg(lean_object* v_t_1595_, lean_object* v_lam_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Expr_ctorElim___redArg(v_t_1595_, v_lam_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam_elim(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_lam_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Expr_ctorElim___redArg(v_t_1599_, v_lam_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim___redArg(lean_object* v_t_1603_, lean_object* v_forallE_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Expr_ctorElim___redArg(v_t_1603_, v_forallE_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE_elim(lean_object* v_motive_1606_, lean_object* v_t_1607_, lean_object* v_h_1608_, lean_object* v_forallE_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Expr_ctorElim___redArg(v_t_1607_, v_forallE_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim___redArg(lean_object* v_t_1611_, lean_object* v_letE_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Expr_ctorElim___redArg(v_t_1611_, v_letE_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE_elim(lean_object* v_motive_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_letE_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Expr_ctorElim___redArg(v_t_1615_, v_letE_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim___redArg(lean_object* v_t_1619_, lean_object* v_lit_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Expr_ctorElim___redArg(v_t_1619_, v_lit_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit_elim(lean_object* v_motive_1622_, lean_object* v_t_1623_, lean_object* v_h_1624_, lean_object* v_lit_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Expr_ctorElim___redArg(v_t_1623_, v_lit_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim___redArg(lean_object* v_t_1627_, lean_object* v_mdata_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Expr_ctorElim___redArg(v_t_1627_, v_mdata_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata_elim(lean_object* v_motive_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_mdata_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Expr_ctorElim___redArg(v_t_1631_, v_mdata_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim___redArg(lean_object* v_t_1635_, lean_object* v_proj_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Expr_ctorElim___redArg(v_t_1635_, v_proj_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj_elim(lean_object* v_motive_1638_, lean_object* v_t_1639_, lean_object* v_h_1640_, lean_object* v_proj_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Expr_ctorElim___redArg(v_t_1639_, v_proj_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* v_a_00___x40___internal___hyg_1644_){
_start:
{
uint64_t v_res_1645_; lean_object* v_r_1646_; 
v_res_1645_ = lean_expr_data(v_a_00___x40___internal___hyg_1644_);
lean_dec_ref(v_a_00___x40___internal___hyg_1644_);
v_r_1646_ = lean_box_uint64(v_res_1645_);
return v_r_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___redArg(lean_object* v_t_1647_, lean_object* v_bvar_1648_, lean_object* v_fvar_1649_, lean_object* v_mvar_1650_, lean_object* v_sort_1651_, lean_object* v_const_1652_, lean_object* v_app_1653_, lean_object* v_lam_1654_, lean_object* v_forallE_1655_, lean_object* v_letE_1656_, lean_object* v_lit_1657_, lean_object* v_mdata_1658_, lean_object* v_proj_1659_){
_start:
{
switch(lean_obj_tag(v_t_1647_))
{
case 0:
{
lean_object* v_deBruijnIndex_1660_; lean_object* v___x_1661_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
v_deBruijnIndex_1660_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_deBruijnIndex_1660_);
lean_dec_ref_known(v_t_1647_, 1);
v___x_1661_ = lean_apply_1(v_bvar_1648_, v_deBruijnIndex_1660_);
return v___x_1661_;
}
case 1:
{
lean_object* v_fvarId_1662_; lean_object* v___x_1663_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_bvar_1648_);
v_fvarId_1662_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_fvarId_1662_);
lean_dec_ref_known(v_t_1647_, 1);
v___x_1663_ = lean_apply_1(v_fvar_1649_, v_fvarId_1662_);
return v___x_1663_;
}
case 2:
{
lean_object* v_mvarId_1664_; lean_object* v___x_1665_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_mvarId_1664_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_mvarId_1664_);
lean_dec_ref_known(v_t_1647_, 1);
v___x_1665_ = lean_apply_1(v_mvar_1650_, v_mvarId_1664_);
return v___x_1665_;
}
case 3:
{
lean_object* v_u_1666_; lean_object* v___x_1667_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_u_1666_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_u_1666_);
lean_dec_ref_known(v_t_1647_, 1);
v___x_1667_ = lean_apply_1(v_sort_1651_, v_u_1666_);
return v___x_1667_;
}
case 4:
{
lean_object* v_declName_1668_; lean_object* v_us_1669_; lean_object* v___x_1670_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_declName_1668_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_declName_1668_);
v_us_1669_ = lean_ctor_get(v_t_1647_, 1);
lean_inc(v_us_1669_);
lean_dec_ref_known(v_t_1647_, 2);
v___x_1670_ = lean_apply_2(v_const_1652_, v_declName_1668_, v_us_1669_);
return v___x_1670_;
}
case 5:
{
lean_object* v_fn_1671_; lean_object* v_arg_1672_; lean_object* v___x_1673_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_fn_1671_ = lean_ctor_get(v_t_1647_, 0);
lean_inc_ref(v_fn_1671_);
v_arg_1672_ = lean_ctor_get(v_t_1647_, 1);
lean_inc_ref(v_arg_1672_);
lean_dec_ref_known(v_t_1647_, 2);
v___x_1673_ = lean_apply_2(v_app_1653_, v_fn_1671_, v_arg_1672_);
return v___x_1673_;
}
case 6:
{
lean_object* v_binderName_1674_; lean_object* v_binderType_1675_; lean_object* v_body_1676_; uint8_t v_binderInfo_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_binderName_1674_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_binderName_1674_);
v_binderType_1675_ = lean_ctor_get(v_t_1647_, 1);
lean_inc_ref(v_binderType_1675_);
v_body_1676_ = lean_ctor_get(v_t_1647_, 2);
lean_inc_ref(v_body_1676_);
v_binderInfo_1677_ = lean_ctor_get_uint8(v_t_1647_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1647_, 3);
v___x_1678_ = lean_box(v_binderInfo_1677_);
v___x_1679_ = lean_apply_4(v_lam_1654_, v_binderName_1674_, v_binderType_1675_, v_body_1676_, v___x_1678_);
return v___x_1679_;
}
case 7:
{
lean_object* v_binderName_1680_; lean_object* v_binderType_1681_; lean_object* v_body_1682_; uint8_t v_binderInfo_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_binderName_1680_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_binderName_1680_);
v_binderType_1681_ = lean_ctor_get(v_t_1647_, 1);
lean_inc_ref(v_binderType_1681_);
v_body_1682_ = lean_ctor_get(v_t_1647_, 2);
lean_inc_ref(v_body_1682_);
v_binderInfo_1683_ = lean_ctor_get_uint8(v_t_1647_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1647_, 3);
v___x_1684_ = lean_box(v_binderInfo_1683_);
v___x_1685_ = lean_apply_4(v_forallE_1655_, v_binderName_1680_, v_binderType_1681_, v_body_1682_, v___x_1684_);
return v___x_1685_;
}
case 8:
{
lean_object* v_declName_1686_; lean_object* v_type_1687_; lean_object* v_value_1688_; lean_object* v_body_1689_; uint8_t v_nondep_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_declName_1686_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_declName_1686_);
v_type_1687_ = lean_ctor_get(v_t_1647_, 1);
lean_inc_ref(v_type_1687_);
v_value_1688_ = lean_ctor_get(v_t_1647_, 2);
lean_inc_ref(v_value_1688_);
v_body_1689_ = lean_ctor_get(v_t_1647_, 3);
lean_inc_ref(v_body_1689_);
v_nondep_1690_ = lean_ctor_get_uint8(v_t_1647_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1647_, 4);
v___x_1691_ = lean_box(v_nondep_1690_);
v___x_1692_ = lean_apply_5(v_letE_1656_, v_declName_1686_, v_type_1687_, v_value_1688_, v_body_1689_, v___x_1691_);
return v___x_1692_;
}
case 9:
{
lean_object* v_a_1693_; lean_object* v___x_1694_; 
lean_dec(v_proj_1659_);
lean_dec(v_mdata_1658_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_a_1693_ = lean_ctor_get(v_t_1647_, 0);
lean_inc_ref(v_a_1693_);
lean_dec_ref_known(v_t_1647_, 1);
v___x_1694_ = lean_apply_1(v_lit_1657_, v_a_1693_);
return v___x_1694_;
}
case 10:
{
lean_object* v_data_1695_; lean_object* v_expr_1696_; lean_object* v___x_1697_; 
lean_dec(v_proj_1659_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_data_1695_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_data_1695_);
v_expr_1696_ = lean_ctor_get(v_t_1647_, 1);
lean_inc_ref(v_expr_1696_);
lean_dec_ref_known(v_t_1647_, 2);
v___x_1697_ = lean_apply_2(v_mdata_1658_, v_data_1695_, v_expr_1696_);
return v___x_1697_;
}
default: 
{
lean_object* v_typeName_1698_; lean_object* v_idx_1699_; lean_object* v_struct_1700_; lean_object* v___x_1701_; 
lean_dec(v_mdata_1658_);
lean_dec(v_lit_1657_);
lean_dec(v_letE_1656_);
lean_dec(v_forallE_1655_);
lean_dec(v_lam_1654_);
lean_dec(v_app_1653_);
lean_dec(v_const_1652_);
lean_dec(v_sort_1651_);
lean_dec(v_mvar_1650_);
lean_dec(v_fvar_1649_);
lean_dec(v_bvar_1648_);
v_typeName_1698_ = lean_ctor_get(v_t_1647_, 0);
lean_inc(v_typeName_1698_);
v_idx_1699_ = lean_ctor_get(v_t_1647_, 1);
lean_inc(v_idx_1699_);
v_struct_1700_ = lean_ctor_get(v_t_1647_, 2);
lean_inc_ref(v_struct_1700_);
lean_dec_ref_known(v_t_1647_, 3);
v___x_1701_ = lean_apply_3(v_proj_1659_, v_typeName_1698_, v_idx_1699_, v_struct_1700_);
return v___x_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* v_motive_1702_, lean_object* v_t_1703_, lean_object* v_bvar_1704_, lean_object* v_fvar_1705_, lean_object* v_mvar_1706_, lean_object* v_sort_1707_, lean_object* v_const_1708_, lean_object* v_app_1709_, lean_object* v_lam_1710_, lean_object* v_forallE_1711_, lean_object* v_letE_1712_, lean_object* v_lit_1713_, lean_object* v_mdata_1714_, lean_object* v_proj_1715_){
_start:
{
switch(lean_obj_tag(v_t_1703_))
{
case 0:
{
lean_object* v_deBruijnIndex_1716_; lean_object* v___x_1717_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
v_deBruijnIndex_1716_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_deBruijnIndex_1716_);
lean_dec_ref_known(v_t_1703_, 1);
v___x_1717_ = lean_apply_1(v_bvar_1704_, v_deBruijnIndex_1716_);
return v___x_1717_;
}
case 1:
{
lean_object* v_fvarId_1718_; lean_object* v___x_1719_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_bvar_1704_);
v_fvarId_1718_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_fvarId_1718_);
lean_dec_ref_known(v_t_1703_, 1);
v___x_1719_ = lean_apply_1(v_fvar_1705_, v_fvarId_1718_);
return v___x_1719_;
}
case 2:
{
lean_object* v_mvarId_1720_; lean_object* v___x_1721_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_mvarId_1720_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_mvarId_1720_);
lean_dec_ref_known(v_t_1703_, 1);
v___x_1721_ = lean_apply_1(v_mvar_1706_, v_mvarId_1720_);
return v___x_1721_;
}
case 3:
{
lean_object* v_u_1722_; lean_object* v___x_1723_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_u_1722_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_u_1722_);
lean_dec_ref_known(v_t_1703_, 1);
v___x_1723_ = lean_apply_1(v_sort_1707_, v_u_1722_);
return v___x_1723_;
}
case 4:
{
lean_object* v_declName_1724_; lean_object* v_us_1725_; lean_object* v___x_1726_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_declName_1724_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_declName_1724_);
v_us_1725_ = lean_ctor_get(v_t_1703_, 1);
lean_inc(v_us_1725_);
lean_dec_ref_known(v_t_1703_, 2);
v___x_1726_ = lean_apply_2(v_const_1708_, v_declName_1724_, v_us_1725_);
return v___x_1726_;
}
case 5:
{
lean_object* v_fn_1727_; lean_object* v_arg_1728_; lean_object* v___x_1729_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_fn_1727_ = lean_ctor_get(v_t_1703_, 0);
lean_inc_ref(v_fn_1727_);
v_arg_1728_ = lean_ctor_get(v_t_1703_, 1);
lean_inc_ref(v_arg_1728_);
lean_dec_ref_known(v_t_1703_, 2);
v___x_1729_ = lean_apply_2(v_app_1709_, v_fn_1727_, v_arg_1728_);
return v___x_1729_;
}
case 6:
{
lean_object* v_binderName_1730_; lean_object* v_binderType_1731_; lean_object* v_body_1732_; uint8_t v_binderInfo_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_binderName_1730_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_binderName_1730_);
v_binderType_1731_ = lean_ctor_get(v_t_1703_, 1);
lean_inc_ref(v_binderType_1731_);
v_body_1732_ = lean_ctor_get(v_t_1703_, 2);
lean_inc_ref(v_body_1732_);
v_binderInfo_1733_ = lean_ctor_get_uint8(v_t_1703_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1703_, 3);
v___x_1734_ = lean_box(v_binderInfo_1733_);
v___x_1735_ = lean_apply_4(v_lam_1710_, v_binderName_1730_, v_binderType_1731_, v_body_1732_, v___x_1734_);
return v___x_1735_;
}
case 7:
{
lean_object* v_binderName_1736_; lean_object* v_binderType_1737_; lean_object* v_body_1738_; uint8_t v_binderInfo_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_binderName_1736_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_binderName_1736_);
v_binderType_1737_ = lean_ctor_get(v_t_1703_, 1);
lean_inc_ref(v_binderType_1737_);
v_body_1738_ = lean_ctor_get(v_t_1703_, 2);
lean_inc_ref(v_body_1738_);
v_binderInfo_1739_ = lean_ctor_get_uint8(v_t_1703_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_t_1703_, 3);
v___x_1740_ = lean_box(v_binderInfo_1739_);
v___x_1741_ = lean_apply_4(v_forallE_1711_, v_binderName_1736_, v_binderType_1737_, v_body_1738_, v___x_1740_);
return v___x_1741_;
}
case 8:
{
lean_object* v_declName_1742_; lean_object* v_type_1743_; lean_object* v_value_1744_; lean_object* v_body_1745_; uint8_t v_nondep_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_declName_1742_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_declName_1742_);
v_type_1743_ = lean_ctor_get(v_t_1703_, 1);
lean_inc_ref(v_type_1743_);
v_value_1744_ = lean_ctor_get(v_t_1703_, 2);
lean_inc_ref(v_value_1744_);
v_body_1745_ = lean_ctor_get(v_t_1703_, 3);
lean_inc_ref(v_body_1745_);
v_nondep_1746_ = lean_ctor_get_uint8(v_t_1703_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_t_1703_, 4);
v___x_1747_ = lean_box(v_nondep_1746_);
v___x_1748_ = lean_apply_5(v_letE_1712_, v_declName_1742_, v_type_1743_, v_value_1744_, v_body_1745_, v___x_1747_);
return v___x_1748_;
}
case 9:
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
lean_dec(v_proj_1715_);
lean_dec(v_mdata_1714_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_a_1749_ = lean_ctor_get(v_t_1703_, 0);
lean_inc_ref(v_a_1749_);
lean_dec_ref_known(v_t_1703_, 1);
v___x_1750_ = lean_apply_1(v_lit_1713_, v_a_1749_);
return v___x_1750_;
}
case 10:
{
lean_object* v_data_1751_; lean_object* v_expr_1752_; lean_object* v___x_1753_; 
lean_dec(v_proj_1715_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_data_1751_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_data_1751_);
v_expr_1752_ = lean_ctor_get(v_t_1703_, 1);
lean_inc_ref(v_expr_1752_);
lean_dec_ref_known(v_t_1703_, 2);
v___x_1753_ = lean_apply_2(v_mdata_1714_, v_data_1751_, v_expr_1752_);
return v___x_1753_;
}
default: 
{
lean_object* v_typeName_1754_; lean_object* v_idx_1755_; lean_object* v_struct_1756_; lean_object* v___x_1757_; 
lean_dec(v_mdata_1714_);
lean_dec(v_lit_1713_);
lean_dec(v_letE_1712_);
lean_dec(v_forallE_1711_);
lean_dec(v_lam_1710_);
lean_dec(v_app_1709_);
lean_dec(v_const_1708_);
lean_dec(v_sort_1707_);
lean_dec(v_mvar_1706_);
lean_dec(v_fvar_1705_);
lean_dec(v_bvar_1704_);
v_typeName_1754_ = lean_ctor_get(v_t_1703_, 0);
lean_inc(v_typeName_1754_);
v_idx_1755_ = lean_ctor_get(v_t_1703_, 1);
lean_inc(v_idx_1755_);
v_struct_1756_ = lean_ctor_get(v_t_1703_, 2);
lean_inc_ref(v_struct_1756_);
lean_dec_ref_known(v_t_1703_, 3);
v___x_1757_ = lean_apply_3(v_proj_1715_, v_typeName_1754_, v_idx_1755_, v_struct_1756_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* v_deBruijnIndex_1758_){
_start:
{
uint64_t v___x_1759_; uint64_t v___x_1760_; uint64_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint32_t v___x_1764_; uint8_t v___x_1765_; uint64_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1759_ = 7ULL;
v___x_1760_ = lean_uint64_of_nat(v_deBruijnIndex_1758_);
v___x_1761_ = lean_uint64_mix_hash(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_deBruijnIndex_1758_, v___x_1762_);
v___x_1764_ = 0;
v___x_1765_ = 0;
v___x_1766_ = lean_expr_mk_data(v___x_1761_, v___x_1763_, v___x_1764_, v___x_1765_, v___x_1765_, v___x_1765_, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1767_, 0, v_deBruijnIndex_1758_);
lean_ctor_set_uint64(v___x_1767_, sizeof(void*)*1, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* v_fvarId_1768_){
_start:
{
uint64_t v___x_1769_; uint64_t v___x_1770_; uint64_t v___x_1771_; lean_object* v___x_1772_; uint32_t v___x_1773_; uint8_t v___x_1774_; uint8_t v___x_1775_; uint64_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1769_ = 13ULL;
v___x_1770_ = l_Lean_instHashableFVarId_hash(v_fvarId_1768_);
v___x_1771_ = lean_uint64_mix_hash(v___x_1769_, v___x_1770_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = 0;
v___x_1774_ = 1;
v___x_1775_ = 0;
v___x_1776_ = lean_expr_mk_data(v___x_1771_, v___x_1772_, v___x_1773_, v___x_1774_, v___x_1775_, v___x_1775_, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(v___x_1777_, 0, v_fvarId_1768_);
lean_ctor_set_uint64(v___x_1777_, sizeof(void*)*1, v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* v_mvarId_1778_){
_start:
{
uint64_t v___x_1779_; uint64_t v___x_1780_; uint64_t v___x_1781_; lean_object* v___x_1782_; uint32_t v___x_1783_; uint8_t v___x_1784_; uint8_t v___x_1785_; uint64_t v___x_1786_; lean_object* v___x_1787_; 
v___x_1779_ = 17ULL;
v___x_1780_ = l_Lean_instHashableMVarId_hash(v_mvarId_1778_);
v___x_1781_ = lean_uint64_mix_hash(v___x_1779_, v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = 0;
v___x_1784_ = 0;
v___x_1785_ = 1;
v___x_1786_ = lean_expr_mk_data(v___x_1781_, v___x_1782_, v___x_1783_, v___x_1784_, v___x_1785_, v___x_1784_, v___x_1784_);
v___x_1787_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_1787_, 0, v_mvarId_1778_);
lean_ctor_set_uint64(v___x_1787_, sizeof(void*)*1, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* v_u_1788_){
_start:
{
uint64_t v___x_1789_; uint64_t v___x_1790_; uint64_t v___x_1791_; lean_object* v___x_1792_; uint32_t v___x_1793_; uint8_t v___x_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; uint64_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1789_ = 11ULL;
v___x_1790_ = l_Lean_Level_hash(v_u_1788_);
v___x_1791_ = lean_uint64_mix_hash(v___x_1789_, v___x_1790_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = 0;
v___x_1794_ = 0;
v___x_1795_ = l_Lean_Level_hasMVar(v_u_1788_);
v___x_1796_ = l_Lean_Level_hasParam(v_u_1788_);
v___x_1797_ = lean_expr_mk_data(v___x_1791_, v___x_1792_, v___x_1793_, v___x_1794_, v___x_1794_, v___x_1795_, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(v___x_1798_, 0, v_u_1788_);
lean_ctor_set_uint64(v___x_1798_, sizeof(void*)*1, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* v_fn_1799_, lean_object* v_arg_1800_){
_start:
{
uint64_t v___x_1801_; uint64_t v___x_1802_; uint64_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_expr_data(v_fn_1799_);
v___x_1802_ = lean_expr_data(v_arg_1800_);
v___x_1803_ = lean_expr_mk_app_data(v___x_1801_, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(v___x_1804_, 0, v_fn_1799_);
lean_ctor_set(v___x_1804_, 1, v_arg_1800_);
lean_ctor_set_uint64(v___x_1804_, sizeof(void*)*2, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* v_binderName_1805_, lean_object* v_binderType_1806_, lean_object* v_body_1807_, uint8_t v_binderInfo_1808_){
_start:
{
uint64_t v___y_1810_; uint8_t v___y_1811_; lean_object* v___y_1812_; uint32_t v___y_1813_; uint8_t v___y_1814_; uint8_t v___y_1815_; uint8_t v___y_1816_; uint64_t v___x_1819_; uint8_t v___x_1820_; uint32_t v___x_1821_; uint64_t v___x_1822_; uint64_t v___y_1824_; uint8_t v___y_1825_; lean_object* v___y_1826_; uint32_t v___y_1827_; uint8_t v___y_1828_; uint8_t v___y_1829_; uint64_t v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; uint32_t v___y_1836_; uint8_t v___y_1837_; uint64_t v___y_1841_; lean_object* v___y_1842_; uint32_t v___y_1843_; uint8_t v___y_1844_; uint64_t v___y_1848_; uint32_t v___y_1849_; lean_object* v___y_1850_; uint32_t v___y_1854_; uint8_t v___x_1869_; uint32_t v___x_1870_; uint8_t v___x_1871_; 
v___x_1819_ = lean_expr_data(v_binderType_1806_);
v___x_1820_ = l_Lean_Expr_Data_approxDepth(v___x_1819_);
v___x_1821_ = lean_uint8_to_uint32(v___x_1820_);
v___x_1822_ = lean_expr_data(v_body_1807_);
v___x_1869_ = l_Lean_Expr_Data_approxDepth(v___x_1822_);
v___x_1870_ = lean_uint8_to_uint32(v___x_1869_);
v___x_1871_ = lean_uint32_dec_le(v___x_1821_, v___x_1870_);
if (v___x_1871_ == 0)
{
v___y_1854_ = v___x_1821_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___x_1870_;
goto v___jp_1853_;
}
v___jp_1809_:
{
uint64_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_expr_mk_data(v___y_1810_, v___y_1812_, v___y_1813_, v___y_1811_, v___y_1815_, v___y_1814_, v___y_1816_);
v___x_1818_ = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(v___x_1818_, 0, v_binderName_1805_);
lean_ctor_set(v___x_1818_, 1, v_binderType_1806_);
lean_ctor_set(v___x_1818_, 2, v_body_1807_);
lean_ctor_set_uint64(v___x_1818_, sizeof(void*)*3, v___x_1817_);
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*3 + 8, v_binderInfo_1808_);
return v___x_1818_;
}
v___jp_1823_:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_Expr_Data_hasLevelParam(v___x_1819_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Lean_Expr_Data_hasLevelParam(v___x_1822_);
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1829_;
v___y_1815_ = v___y_1828_;
v___y_1816_ = v___x_1831_;
goto v___jp_1809_;
}
else
{
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1827_;
v___y_1814_ = v___y_1829_;
v___y_1815_ = v___y_1828_;
v___y_1816_ = v___x_1830_;
goto v___jp_1809_;
}
}
v___jp_1832_:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1819_);
if (v___x_1838_ == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1822_);
v___y_1824_ = v___y_1833_;
v___y_1825_ = v___y_1834_;
v___y_1826_ = v___y_1835_;
v___y_1827_ = v___y_1836_;
v___y_1828_ = v___y_1837_;
v___y_1829_ = v___x_1839_;
goto v___jp_1823_;
}
else
{
v___y_1824_ = v___y_1833_;
v___y_1825_ = v___y_1834_;
v___y_1826_ = v___y_1835_;
v___y_1827_ = v___y_1836_;
v___y_1828_ = v___y_1837_;
v___y_1829_ = v___x_1838_;
goto v___jp_1823_;
}
}
v___jp_1840_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Expr_Data_hasExprMVar(v___x_1819_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_Expr_Data_hasExprMVar(v___x_1822_);
v___y_1833_ = v___y_1841_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___y_1843_;
v___y_1837_ = v___x_1846_;
goto v___jp_1832_;
}
else
{
v___y_1833_ = v___y_1841_;
v___y_1834_ = v___y_1844_;
v___y_1835_ = v___y_1842_;
v___y_1836_ = v___y_1843_;
v___y_1837_ = v___x_1845_;
goto v___jp_1832_;
}
}
v___jp_1847_:
{
uint8_t v___x_1851_; 
v___x_1851_ = l_Lean_Expr_Data_hasFVar(v___x_1819_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_Expr_Data_hasFVar(v___x_1822_);
v___y_1841_ = v___y_1848_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1849_;
v___y_1844_ = v___x_1852_;
goto v___jp_1840_;
}
else
{
v___y_1841_ = v___y_1848_;
v___y_1842_ = v___y_1850_;
v___y_1843_ = v___y_1849_;
v___y_1844_ = v___x_1851_;
goto v___jp_1840_;
}
}
v___jp_1853_:
{
lean_object* v___x_1855_; uint32_t v___x_1856_; uint32_t v___x_1857_; uint64_t v___x_1858_; uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; uint64_t v___x_1862_; uint32_t v___x_1863_; lean_object* v___x_1864_; uint32_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = 1;
v___x_1857_ = lean_uint32_add(v___y_1854_, v___x_1856_);
v___x_1858_ = lean_uint32_to_uint64(v___x_1857_);
v___x_1859_ = l_Lean_Expr_Data_hash(v___x_1819_);
v___x_1860_ = l_Lean_Expr_Data_hash(v___x_1822_);
v___x_1861_ = lean_uint64_mix_hash(v___x_1859_, v___x_1860_);
v___x_1862_ = lean_uint64_mix_hash(v___x_1858_, v___x_1861_);
v___x_1863_ = l_Lean_Expr_Data_looseBVarRange(v___x_1819_);
v___x_1864_ = lean_uint32_to_nat(v___x_1863_);
v___x_1865_ = l_Lean_Expr_Data_looseBVarRange(v___x_1822_);
v___x_1866_ = lean_uint32_to_nat(v___x_1865_);
v___x_1867_ = lean_nat_sub(v___x_1866_, v___x_1855_);
lean_dec(v___x_1866_);
v___x_1868_ = lean_nat_dec_le(v___x_1864_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_dec(v___x_1867_);
v___y_1848_ = v___x_1862_;
v___y_1849_ = v___x_1857_;
v___y_1850_ = v___x_1864_;
goto v___jp_1847_;
}
else
{
lean_dec(v___x_1864_);
v___y_1848_ = v___x_1862_;
v___y_1849_ = v___x_1857_;
v___y_1850_ = v___x_1867_;
goto v___jp_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* v_binderName_1872_, lean_object* v_binderType_1873_, lean_object* v_body_1874_, lean_object* v_binderInfo_1875_){
_start:
{
uint8_t v_binderInfo_boxed_1876_; lean_object* v_res_1877_; 
v_binderInfo_boxed_1876_ = lean_unbox(v_binderInfo_1875_);
v_res_1877_ = l_Lean_Expr_lam___override(v_binderName_1872_, v_binderType_1873_, v_body_1874_, v_binderInfo_boxed_1876_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* v_binderName_1878_, lean_object* v_binderType_1879_, lean_object* v_body_1880_, uint8_t v_binderInfo_1881_){
_start:
{
uint64_t v___y_1883_; uint32_t v___y_1884_; uint8_t v___y_1885_; uint8_t v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1888_; uint8_t v___y_1889_; uint64_t v___x_1892_; uint8_t v___x_1893_; uint32_t v___x_1894_; uint64_t v___x_1895_; uint64_t v___y_1897_; uint32_t v___y_1898_; uint8_t v___y_1899_; uint8_t v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; uint64_t v___y_1906_; uint32_t v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint64_t v___y_1914_; uint32_t v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; uint64_t v___y_1921_; uint32_t v___y_1922_; lean_object* v___y_1923_; uint32_t v___y_1927_; uint8_t v___x_1942_; uint32_t v___x_1943_; uint8_t v___x_1944_; 
v___x_1892_ = lean_expr_data(v_binderType_1879_);
v___x_1893_ = l_Lean_Expr_Data_approxDepth(v___x_1892_);
v___x_1894_ = lean_uint8_to_uint32(v___x_1893_);
v___x_1895_ = lean_expr_data(v_body_1880_);
v___x_1942_ = l_Lean_Expr_Data_approxDepth(v___x_1895_);
v___x_1943_ = lean_uint8_to_uint32(v___x_1942_);
v___x_1944_ = lean_uint32_dec_le(v___x_1894_, v___x_1943_);
if (v___x_1944_ == 0)
{
v___y_1927_ = v___x_1894_;
goto v___jp_1926_;
}
else
{
v___y_1927_ = v___x_1943_;
goto v___jp_1926_;
}
v___jp_1882_:
{
uint64_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_expr_mk_data(v___y_1883_, v___y_1888_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1889_);
v___x_1891_ = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(v___x_1891_, 0, v_binderName_1878_);
lean_ctor_set(v___x_1891_, 1, v_binderType_1879_);
lean_ctor_set(v___x_1891_, 2, v_body_1880_);
lean_ctor_set_uint64(v___x_1891_, sizeof(void*)*3, v___x_1890_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 8, v_binderInfo_1881_);
return v___x_1891_;
}
v___jp_1896_:
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_Expr_Data_hasLevelParam(v___x_1892_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Expr_Data_hasLevelParam(v___x_1895_);
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___y_1898_;
v___y_1885_ = v___y_1899_;
v___y_1886_ = v___y_1900_;
v___y_1887_ = v___y_1902_;
v___y_1888_ = v___y_1901_;
v___y_1889_ = v___x_1904_;
goto v___jp_1882_;
}
else
{
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___y_1898_;
v___y_1885_ = v___y_1899_;
v___y_1886_ = v___y_1900_;
v___y_1887_ = v___y_1902_;
v___y_1888_ = v___y_1901_;
v___y_1889_ = v___x_1903_;
goto v___jp_1882_;
}
}
v___jp_1905_:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1892_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1895_);
v___y_1897_ = v___y_1906_;
v___y_1898_ = v___y_1907_;
v___y_1899_ = v___y_1908_;
v___y_1900_ = v___y_1910_;
v___y_1901_ = v___y_1909_;
v___y_1902_ = v___x_1912_;
goto v___jp_1896_;
}
else
{
v___y_1897_ = v___y_1906_;
v___y_1898_ = v___y_1907_;
v___y_1899_ = v___y_1908_;
v___y_1900_ = v___y_1910_;
v___y_1901_ = v___y_1909_;
v___y_1902_ = v___x_1911_;
goto v___jp_1896_;
}
}
v___jp_1913_:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Expr_Data_hasExprMVar(v___x_1892_);
if (v___x_1918_ == 0)
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_Expr_Data_hasExprMVar(v___x_1895_);
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1917_;
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___x_1919_;
goto v___jp_1905_;
}
else
{
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___y_1917_;
v___y_1909_ = v___y_1916_;
v___y_1910_ = v___x_1918_;
goto v___jp_1905_;
}
}
v___jp_1920_:
{
uint8_t v___x_1924_; 
v___x_1924_ = l_Lean_Expr_Data_hasFVar(v___x_1892_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = l_Lean_Expr_Data_hasFVar(v___x_1895_);
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___y_1923_;
v___y_1917_ = v___x_1925_;
goto v___jp_1913_;
}
else
{
v___y_1914_ = v___y_1921_;
v___y_1915_ = v___y_1922_;
v___y_1916_ = v___y_1923_;
v___y_1917_ = v___x_1924_;
goto v___jp_1913_;
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; uint32_t v___x_1929_; uint32_t v___x_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v___x_1933_; uint64_t v___x_1934_; uint64_t v___x_1935_; uint32_t v___x_1936_; lean_object* v___x_1937_; uint32_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = 1;
v___x_1930_ = lean_uint32_add(v___y_1927_, v___x_1929_);
v___x_1931_ = lean_uint32_to_uint64(v___x_1930_);
v___x_1932_ = l_Lean_Expr_Data_hash(v___x_1892_);
v___x_1933_ = l_Lean_Expr_Data_hash(v___x_1895_);
v___x_1934_ = lean_uint64_mix_hash(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_uint64_mix_hash(v___x_1931_, v___x_1934_);
v___x_1936_ = l_Lean_Expr_Data_looseBVarRange(v___x_1892_);
v___x_1937_ = lean_uint32_to_nat(v___x_1936_);
v___x_1938_ = l_Lean_Expr_Data_looseBVarRange(v___x_1895_);
v___x_1939_ = lean_uint32_to_nat(v___x_1938_);
v___x_1940_ = lean_nat_sub(v___x_1939_, v___x_1928_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_nat_dec_le(v___x_1937_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_dec(v___x_1940_);
v___y_1921_ = v___x_1935_;
v___y_1922_ = v___x_1930_;
v___y_1923_ = v___x_1937_;
goto v___jp_1920_;
}
else
{
lean_dec(v___x_1937_);
v___y_1921_ = v___x_1935_;
v___y_1922_ = v___x_1930_;
v___y_1923_ = v___x_1940_;
goto v___jp_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* v_binderName_1945_, lean_object* v_binderType_1946_, lean_object* v_body_1947_, lean_object* v_binderInfo_1948_){
_start:
{
uint8_t v_binderInfo_boxed_1949_; lean_object* v_res_1950_; 
v_binderInfo_boxed_1949_ = lean_unbox(v_binderInfo_1948_);
v_res_1950_ = l_Lean_Expr_forallE___override(v_binderName_1945_, v_binderType_1946_, v_body_1947_, v_binderInfo_boxed_1949_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* v_declName_1951_, lean_object* v_type_1952_, lean_object* v_value_1953_, lean_object* v_body_1954_, uint8_t v_nondep_1955_){
_start:
{
uint8_t v___y_1957_; uint8_t v___y_1958_; uint32_t v___y_1959_; uint8_t v___y_1960_; lean_object* v___y_1961_; uint64_t v___y_1962_; uint8_t v___y_1963_; uint64_t v___x_1966_; uint8_t v___x_1967_; uint32_t v___x_1968_; uint64_t v___x_1969_; uint8_t v___y_1971_; uint32_t v___y_1972_; lean_object* v___y_1973_; uint8_t v___y_1974_; uint64_t v___y_1975_; uint64_t v___y_1976_; uint8_t v___y_1977_; uint8_t v___y_1982_; uint32_t v___y_1983_; lean_object* v___y_1984_; uint64_t v___y_1985_; uint64_t v___y_1986_; uint8_t v___y_1987_; uint32_t v___y_1992_; lean_object* v___y_1993_; uint64_t v___y_1994_; uint64_t v___y_1995_; uint8_t v___y_1996_; uint32_t v___y_2001_; uint64_t v___y_2002_; uint64_t v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2009_; uint32_t v___y_2010_; uint64_t v___y_2011_; uint64_t v___y_2012_; lean_object* v___y_2013_; uint64_t v___y_2019_; uint32_t v___y_2020_; uint32_t v___y_2037_; uint8_t v___x_2042_; uint32_t v___x_2043_; uint8_t v___x_2044_; 
v___x_1966_ = lean_expr_data(v_type_1952_);
v___x_1967_ = l_Lean_Expr_Data_approxDepth(v___x_1966_);
v___x_1968_ = lean_uint8_to_uint32(v___x_1967_);
v___x_1969_ = lean_expr_data(v_value_1953_);
v___x_2042_ = l_Lean_Expr_Data_approxDepth(v___x_1969_);
v___x_2043_ = lean_uint8_to_uint32(v___x_2042_);
v___x_2044_ = lean_uint32_dec_le(v___x_1968_, v___x_2043_);
if (v___x_2044_ == 0)
{
v___y_2037_ = v___x_1968_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v___x_2043_;
goto v___jp_2036_;
}
v___jp_1956_:
{
uint64_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_expr_mk_data(v___y_1962_, v___y_1961_, v___y_1959_, v___y_1958_, v___y_1960_, v___y_1957_, v___y_1963_);
v___x_1965_ = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(v___x_1965_, 0, v_declName_1951_);
lean_ctor_set(v___x_1965_, 1, v_type_1952_);
lean_ctor_set(v___x_1965_, 2, v_value_1953_);
lean_ctor_set(v___x_1965_, 3, v_body_1954_);
lean_ctor_set_uint64(v___x_1965_, sizeof(void*)*4, v___x_1964_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*4 + 8, v_nondep_1955_);
return v___x_1965_;
}
v___jp_1970_:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_Expr_Data_hasLevelParam(v___x_1966_);
if (v___x_1978_ == 0)
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_Expr_Data_hasLevelParam(v___x_1969_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Expr_Data_hasLevelParam(v___y_1975_);
v___y_1957_ = v___y_1977_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v___y_1973_;
v___y_1962_ = v___y_1976_;
v___y_1963_ = v___x_1980_;
goto v___jp_1956_;
}
else
{
v___y_1957_ = v___y_1977_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v___y_1973_;
v___y_1962_ = v___y_1976_;
v___y_1963_ = v___x_1979_;
goto v___jp_1956_;
}
}
else
{
v___y_1957_ = v___y_1977_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1972_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v___y_1973_;
v___y_1962_ = v___y_1976_;
v___y_1963_ = v___x_1978_;
goto v___jp_1956_;
}
}
v___jp_1981_:
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1966_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Expr_Data_hasLevelMVar(v___x_1969_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Expr_Data_hasLevelMVar(v___y_1985_);
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1983_;
v___y_1973_ = v___y_1984_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___x_1990_;
goto v___jp_1970_;
}
else
{
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1983_;
v___y_1973_ = v___y_1984_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___x_1989_;
goto v___jp_1970_;
}
}
else
{
v___y_1971_ = v___y_1982_;
v___y_1972_ = v___y_1983_;
v___y_1973_ = v___y_1984_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___x_1988_;
goto v___jp_1970_;
}
}
v___jp_1991_:
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Lean_Expr_Data_hasExprMVar(v___x_1966_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Expr_Data_hasExprMVar(v___x_1969_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_Expr_Data_hasExprMVar(v___y_1994_);
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1992_;
v___y_1984_ = v___y_1993_;
v___y_1985_ = v___y_1994_;
v___y_1986_ = v___y_1995_;
v___y_1987_ = v___x_1999_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1992_;
v___y_1984_ = v___y_1993_;
v___y_1985_ = v___y_1994_;
v___y_1986_ = v___y_1995_;
v___y_1987_ = v___x_1998_;
goto v___jp_1981_;
}
}
else
{
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1992_;
v___y_1984_ = v___y_1993_;
v___y_1985_ = v___y_1994_;
v___y_1986_ = v___y_1995_;
v___y_1987_ = v___x_1997_;
goto v___jp_1981_;
}
}
v___jp_2000_:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Expr_Data_hasFVar(v___x_1966_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Expr_Data_hasFVar(v___x_1969_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Expr_Data_hasFVar(v___y_2002_);
v___y_1992_ = v___y_2001_;
v___y_1993_ = v___y_2004_;
v___y_1994_ = v___y_2002_;
v___y_1995_ = v___y_2003_;
v___y_1996_ = v___x_2007_;
goto v___jp_1991_;
}
else
{
v___y_1992_ = v___y_2001_;
v___y_1993_ = v___y_2004_;
v___y_1994_ = v___y_2002_;
v___y_1995_ = v___y_2003_;
v___y_1996_ = v___x_2006_;
goto v___jp_1991_;
}
}
else
{
v___y_1992_ = v___y_2001_;
v___y_1993_ = v___y_2004_;
v___y_1994_ = v___y_2002_;
v___y_1995_ = v___y_2003_;
v___y_1996_ = v___x_2005_;
goto v___jp_1991_;
}
}
v___jp_2008_:
{
uint32_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2014_ = l_Lean_Expr_Data_looseBVarRange(v___y_2011_);
v___x_2015_ = lean_uint32_to_nat(v___x_2014_);
v___x_2016_ = lean_nat_sub(v___x_2015_, v___y_2009_);
lean_dec(v___x_2015_);
v___x_2017_ = lean_nat_dec_le(v___y_2013_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_dec(v___x_2016_);
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2012_;
v___y_2004_ = v___y_2013_;
goto v___jp_2000_;
}
else
{
lean_dec(v___y_2013_);
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2011_;
v___y_2003_ = v___y_2012_;
v___y_2004_ = v___x_2016_;
goto v___jp_2000_;
}
}
v___jp_2018_:
{
lean_object* v___x_2021_; uint32_t v___x_2022_; uint32_t v___x_2023_; uint64_t v___x_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; uint64_t v___x_2028_; uint64_t v___x_2029_; uint64_t v___x_2030_; uint32_t v___x_2031_; lean_object* v___x_2032_; uint32_t v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = 1;
v___x_2023_ = lean_uint32_add(v___y_2020_, v___x_2022_);
v___x_2024_ = lean_uint32_to_uint64(v___x_2023_);
v___x_2025_ = l_Lean_Expr_Data_hash(v___x_1966_);
v___x_2026_ = l_Lean_Expr_Data_hash(v___x_1969_);
v___x_2027_ = l_Lean_Expr_Data_hash(v___y_2019_);
v___x_2028_ = lean_uint64_mix_hash(v___x_2026_, v___x_2027_);
v___x_2029_ = lean_uint64_mix_hash(v___x_2025_, v___x_2028_);
v___x_2030_ = lean_uint64_mix_hash(v___x_2024_, v___x_2029_);
v___x_2031_ = l_Lean_Expr_Data_looseBVarRange(v___x_1966_);
v___x_2032_ = lean_uint32_to_nat(v___x_2031_);
v___x_2033_ = l_Lean_Expr_Data_looseBVarRange(v___x_1969_);
v___x_2034_ = lean_uint32_to_nat(v___x_2033_);
v___x_2035_ = lean_nat_dec_le(v___x_2032_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_dec(v___x_2034_);
v___y_2009_ = v___x_2021_;
v___y_2010_ = v___x_2023_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___x_2030_;
v___y_2013_ = v___x_2032_;
goto v___jp_2008_;
}
else
{
lean_dec(v___x_2032_);
v___y_2009_ = v___x_2021_;
v___y_2010_ = v___x_2023_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___x_2030_;
v___y_2013_ = v___x_2034_;
goto v___jp_2008_;
}
}
v___jp_2036_:
{
uint64_t v___x_2038_; uint8_t v___x_2039_; uint32_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2038_ = lean_expr_data(v_body_1954_);
v___x_2039_ = l_Lean_Expr_Data_approxDepth(v___x_2038_);
v___x_2040_ = lean_uint8_to_uint32(v___x_2039_);
v___x_2041_ = lean_uint32_dec_le(v___y_2037_, v___x_2040_);
if (v___x_2041_ == 0)
{
v___y_2019_ = v___x_2038_;
v___y_2020_ = v___y_2037_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v___x_2038_;
v___y_2020_ = v___x_2040_;
goto v___jp_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* v_declName_2045_, lean_object* v_type_2046_, lean_object* v_value_2047_, lean_object* v_body_2048_, lean_object* v_nondep_2049_){
_start:
{
uint8_t v_nondep_boxed_2050_; lean_object* v_res_2051_; 
v_nondep_boxed_2050_ = lean_unbox(v_nondep_2049_);
v_res_2051_ = l_Lean_Expr_letE___override(v_declName_2045_, v_type_2046_, v_value_2047_, v_body_2048_, v_nondep_boxed_2050_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* v_a_2052_){
_start:
{
uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; lean_object* v___x_2056_; uint32_t v___x_2057_; uint8_t v___x_2058_; uint64_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2053_ = 3ULL;
v___x_2054_ = l_Lean_Literal_hash(v_a_2052_);
v___x_2055_ = lean_uint64_mix_hash(v___x_2053_, v___x_2054_);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = 0;
v___x_2058_ = 0;
v___x_2059_ = lean_expr_mk_data(v___x_2055_, v___x_2056_, v___x_2057_, v___x_2058_, v___x_2058_, v___x_2058_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(v___x_2060_, 0, v_a_2052_);
lean_ctor_set_uint64(v___x_2060_, sizeof(void*)*1, v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* v_data_2061_, lean_object* v_expr_2062_){
_start:
{
uint64_t v___x_2063_; uint8_t v___x_2064_; uint32_t v___x_2065_; uint32_t v___x_2066_; uint32_t v___x_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint32_t v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; uint64_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2063_ = lean_expr_data(v_expr_2062_);
v___x_2064_ = l_Lean_Expr_Data_approxDepth(v___x_2063_);
v___x_2065_ = lean_uint8_to_uint32(v___x_2064_);
v___x_2066_ = 1;
v___x_2067_ = lean_uint32_add(v___x_2065_, v___x_2066_);
v___x_2068_ = lean_uint32_to_uint64(v___x_2067_);
v___x_2069_ = l_Lean_Expr_Data_hash(v___x_2063_);
v___x_2070_ = lean_uint64_mix_hash(v___x_2068_, v___x_2069_);
v___x_2071_ = l_Lean_Expr_Data_looseBVarRange(v___x_2063_);
v___x_2072_ = lean_uint32_to_nat(v___x_2071_);
v___x_2073_ = l_Lean_Expr_Data_hasFVar(v___x_2063_);
v___x_2074_ = l_Lean_Expr_Data_hasExprMVar(v___x_2063_);
v___x_2075_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2063_);
v___x_2076_ = l_Lean_Expr_Data_hasLevelParam(v___x_2063_);
v___x_2077_ = lean_expr_mk_data(v___x_2070_, v___x_2072_, v___x_2067_, v___x_2073_, v___x_2074_, v___x_2075_, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(v___x_2078_, 0, v_data_2061_);
lean_ctor_set(v___x_2078_, 1, v_expr_2062_);
lean_ctor_set_uint64(v___x_2078_, sizeof(void*)*2, v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* v_typeName_2079_, lean_object* v_idx_2080_, lean_object* v_struct_2081_){
_start:
{
uint64_t v___x_2082_; uint8_t v___x_2083_; uint32_t v___x_2084_; uint32_t v___x_2085_; uint32_t v___x_2086_; uint64_t v___x_2087_; uint64_t v___y_2089_; 
v___x_2082_ = lean_expr_data(v_struct_2081_);
v___x_2083_ = l_Lean_Expr_Data_approxDepth(v___x_2082_);
v___x_2084_ = lean_uint8_to_uint32(v___x_2083_);
v___x_2085_ = 1;
v___x_2086_ = lean_uint32_add(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_uint32_to_uint64(v___x_2086_);
if (lean_obj_tag(v_typeName_2079_) == 0)
{
uint64_t v___x_2103_; 
v___x_2103_ = 1723ULL;
v___y_2089_ = v___x_2103_;
goto v___jp_2088_;
}
else
{
uint64_t v_hash_2104_; 
v_hash_2104_ = lean_ctor_get_uint64(v_typeName_2079_, sizeof(void*)*2);
v___y_2089_ = v_hash_2104_;
goto v___jp_2088_;
}
v___jp_2088_:
{
uint64_t v___x_2090_; uint64_t v___x_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; uint32_t v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; uint8_t v___x_2098_; uint8_t v___x_2099_; uint8_t v___x_2100_; uint64_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2090_ = lean_uint64_of_nat(v_idx_2080_);
v___x_2091_ = l_Lean_Expr_Data_hash(v___x_2082_);
v___x_2092_ = lean_uint64_mix_hash(v___x_2090_, v___x_2091_);
v___x_2093_ = lean_uint64_mix_hash(v___y_2089_, v___x_2092_);
v___x_2094_ = lean_uint64_mix_hash(v___x_2087_, v___x_2093_);
v___x_2095_ = l_Lean_Expr_Data_looseBVarRange(v___x_2082_);
v___x_2096_ = lean_uint32_to_nat(v___x_2095_);
v___x_2097_ = l_Lean_Expr_Data_hasFVar(v___x_2082_);
v___x_2098_ = l_Lean_Expr_Data_hasExprMVar(v___x_2082_);
v___x_2099_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2082_);
v___x_2100_ = l_Lean_Expr_Data_hasLevelParam(v___x_2082_);
v___x_2101_ = lean_expr_mk_data(v___x_2094_, v___x_2096_, v___x_2086_, v___x_2097_, v___x_2098_, v___x_2099_, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(v___x_2102_, 0, v_typeName_2079_);
lean_ctor_set(v___x_2102_, 1, v_idx_2080_);
lean_ctor_set(v___x_2102_, 2, v_struct_2081_);
lean_ctor_set_uint64(v___x_2102_, sizeof(void*)*3, v___x_2101_);
return v___x_2102_;
}
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__5(lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
uint8_t v___x_2106_; 
v___x_2106_ = 0;
return v___x_2106_;
}
else
{
lean_object* v_head_2107_; lean_object* v_tail_2108_; uint8_t v___x_2109_; 
v_head_2107_ = lean_ctor_get(v_x_2105_, 0);
v_tail_2108_ = lean_ctor_get(v_x_2105_, 1);
v___x_2109_ = l_Lean_Level_hasMVar(v_head_2107_);
if (v___x_2109_ == 0)
{
v_x_2105_ = v_tail_2108_;
goto _start;
}
else
{
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__5___boxed(lean_object* v_x_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_x_2111_);
lean_dec(v_x_2111_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Expr_const___override_spec__6(lean_object* v_x_2114_){
_start:
{
if (lean_obj_tag(v_x_2114_) == 0)
{
uint8_t v___x_2115_; 
v___x_2115_ = 0;
return v___x_2115_;
}
else
{
lean_object* v_head_2116_; lean_object* v_tail_2117_; uint8_t v___x_2118_; 
v_head_2116_ = lean_ctor_get(v_x_2114_, 0);
v_tail_2117_ = lean_ctor_get(v_x_2114_, 1);
v___x_2118_ = l_Lean_Level_hasParam(v_head_2116_);
if (v___x_2118_ == 0)
{
v_x_2114_ = v_tail_2117_;
goto _start;
}
else
{
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Expr_const___override_spec__6___boxed(lean_object* v_x_2120_){
_start:
{
uint8_t v_res_2121_; lean_object* v_r_2122_; 
v_res_2121_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_x_2120_);
lean_dec(v_x_2120_);
v_r_2122_ = lean_box(v_res_2121_);
return v_r_2122_;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Expr_const___override_spec__4(uint64_t v_x_2123_, lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
return v_x_2123_;
}
else
{
lean_object* v_head_2125_; lean_object* v_tail_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; 
v_head_2125_ = lean_ctor_get(v_x_2124_, 0);
v_tail_2126_ = lean_ctor_get(v_x_2124_, 1);
v___x_2127_ = l_Lean_Level_hash(v_head_2125_);
v___x_2128_ = lean_uint64_mix_hash(v_x_2123_, v___x_2127_);
v_x_2123_ = v___x_2128_;
v_x_2124_ = v_tail_2126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Expr_const___override_spec__4___boxed(lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
uint64_t v_x_1645__boxed_2132_; uint64_t v_res_2133_; lean_object* v_r_2134_; 
v_x_1645__boxed_2132_ = lean_unbox_uint64(v_x_2130_);
lean_dec_ref(v_x_2130_);
v_res_2133_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v_x_1645__boxed_2132_, v_x_2131_);
lean_dec(v_x_2131_);
v_r_2134_ = lean_box_uint64(v_res_2133_);
return v_r_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* v_declName_2135_, lean_object* v_us_2136_){
_start:
{
uint64_t v___x_2137_; uint64_t v___y_2139_; 
v___x_2137_ = 5ULL;
if (lean_obj_tag(v_declName_2135_) == 0)
{
uint64_t v___x_2151_; 
v___x_2151_ = 1723ULL;
v___y_2139_ = v___x_2151_;
goto v___jp_2138_;
}
else
{
uint64_t v_hash_2152_; 
v_hash_2152_ = lean_ctor_get_uint64(v_declName_2135_, sizeof(void*)*2);
v___y_2139_ = v_hash_2152_;
goto v___jp_2138_;
}
v___jp_2138_:
{
uint64_t v___x_2140_; uint64_t v___x_2141_; uint64_t v___x_2142_; uint64_t v___x_2143_; lean_object* v___x_2144_; uint32_t v___x_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; uint8_t v___x_2148_; uint64_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2140_ = 7ULL;
v___x_2141_ = l_List_foldl___at___00Lean_Expr_const___override_spec__4(v___x_2140_, v_us_2136_);
v___x_2142_ = lean_uint64_mix_hash(v___y_2139_, v___x_2141_);
v___x_2143_ = lean_uint64_mix_hash(v___x_2137_, v___x_2142_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = 0;
v___x_2146_ = 0;
v___x_2147_ = l_List_any___at___00Lean_Expr_const___override_spec__5(v_us_2136_);
v___x_2148_ = l_List_any___at___00Lean_Expr_const___override_spec__6(v_us_2136_);
v___x_2149_ = lean_expr_mk_data(v___x_2143_, v___x_2144_, v___x_2145_, v___x_2146_, v___x_2146_, v___x_2147_, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(v___x_2150_, 0, v_declName_2135_);
lean_ctor_set(v___x_2150_, 1, v_us_2136_);
lean_ctor_set_uint64(v___x_2150_, sizeof(void*)*2, v___x_2149_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = l_Lean_instReprLevel_repr(v___y_2153_, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
lean_dec(v_x_2156_);
return v_x_2157_;
}
else
{
lean_object* v_head_2159_; lean_object* v_tail_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2171_; 
v_head_2159_ = lean_ctor_get(v_x_2158_, 0);
v_tail_2160_ = lean_ctor_get(v_x_2158_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_x_2158_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2162_ = v_x_2158_;
v_isShared_2163_ = v_isSharedCheck_2171_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_tail_2160_);
lean_inc(v_head_2159_);
lean_dec(v_x_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2171_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
lean_inc(v_x_2156_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 5);
lean_ctor_set(v___x_2162_, 1, v_x_2156_);
lean_ctor_set(v___x_2162_, 0, v_x_2157_);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_x_2157_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_x_2156_);
v___x_2165_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l_Lean_instReprLevel_repr(v_head_2159_, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2165_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v_x_2157_ = v___x_2168_;
v_x_2158_ = v_tail_2160_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
lean_dec(v_x_2172_);
return v_x_2173_;
}
else
{
lean_object* v_head_2175_; lean_object* v_tail_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2187_; 
v_head_2175_ = lean_ctor_get(v_x_2174_, 0);
v_tail_2176_ = lean_ctor_get(v_x_2174_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2174_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2178_ = v_x_2174_;
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_tail_2176_);
lean_inc(v_head_2175_);
lean_dec(v_x_2174_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
lean_inc(v_x_2172_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 5);
lean_ctor_set(v___x_2178_, 1, v_x_2172_);
lean_ctor_set(v___x_2178_, 0, v_x_2173_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_x_2173_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_x_2172_);
v___x_2181_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = l_Lean_instReprLevel_repr(v_head_2175_, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2181_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1_spec__3(v_x_2172_, v___x_2184_, v_tail_2176_);
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
lean_object* v___x_2190_; 
lean_dec(v_x_2189_);
v___x_2190_ = lean_box(0);
return v___x_2190_;
}
else
{
lean_object* v_tail_2191_; 
v_tail_2191_ = lean_ctor_get(v_x_2188_, 1);
if (lean_obj_tag(v_tail_2191_) == 0)
{
lean_object* v_head_2192_; lean_object* v___x_2193_; 
lean_dec(v_x_2189_);
v_head_2192_ = lean_ctor_get(v_x_2188_, 0);
lean_inc(v_head_2192_);
lean_dec_ref_known(v_x_2188_, 2);
v___x_2193_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2192_);
return v___x_2193_;
}
else
{
lean_object* v_head_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_inc(v_tail_2191_);
v_head_2194_ = lean_ctor_get(v_x_2188_, 0);
lean_inc(v_head_2194_);
lean_dec_ref_known(v_x_2188_, 2);
v___x_2195_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0___lam__0(v_head_2194_);
v___x_2196_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0_spec__1(v_x_2189_, v___x_2195_, v_tail_2191_);
return v___x_2196_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__2));
v___x_2209_ = lean_string_length(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__7);
v___x_2211_ = lean_nat_to_int(v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(lean_object* v_a_2216_){
_start:
{
if (lean_obj_tag(v_a_2216_) == 0)
{
lean_object* v___x_2217_; 
v___x_2217_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__1));
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
v___x_2218_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__5));
v___x_2219_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__0(v_a_2216_, v___x_2218_);
v___x_2220_ = lean_obj_once(&l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8, &l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8_once, _init_l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__8);
v___x_2221_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__9));
v___x_2222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2219_);
v___x_2223_ = ((lean_object*)(l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg___closed__10));
v___x_2224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2220_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = 0;
v___x_2227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2226_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr(lean_object* v_x_2300_, lean_object* v_prec_2301_){
_start:
{
switch(lean_obj_tag(v_x_2300_))
{
case 0:
{
lean_object* v_deBruijnIndex_2302_; lean_object* v___y_2304_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_deBruijnIndex_2302_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_deBruijnIndex_2302_);
lean_dec_ref_known(v_x_2300_, 1);
v___x_2313_ = lean_unsigned_to_nat(1024u);
v___x_2314_ = lean_nat_dec_le(v___x_2313_, v_prec_2301_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2304_ = v___x_2315_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2304_ = v___x_2316_;
goto v___jp_2303_;
}
v___jp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2305_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__2));
v___x_2306_ = l_Nat_reprFast(v_deBruijnIndex_2302_);
v___x_2307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2305_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
lean_inc(v___y_2304_);
v___x_2309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___y_2304_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = 0;
v___x_2311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*1, v___x_2310_);
v___x_2312_ = l_Repr_addAppParen(v___x_2311_, v_prec_2301_);
return v___x_2312_;
}
}
case 1:
{
lean_object* v_fvarId_2317_; lean_object* v___y_2319_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_fvarId_2317_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_fvarId_2317_);
lean_dec_ref_known(v_x_2300_, 1);
v___x_2328_ = lean_unsigned_to_nat(1024u);
v___x_2329_ = lean_nat_dec_le(v___x_2328_, v_prec_2301_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2319_ = v___x_2330_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2319_ = v___x_2331_;
goto v___jp_2318_;
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2320_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__5));
v___x_2321_ = lean_unsigned_to_nat(1024u);
v___x_2322_ = l_Lean_Name_reprPrec(v_fvarId_2317_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2320_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_inc(v___y_2319_);
v___x_2324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___y_2319_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = 0;
v___x_2326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*1, v___x_2325_);
v___x_2327_ = l_Repr_addAppParen(v___x_2326_, v_prec_2301_);
return v___x_2327_;
}
}
case 2:
{
lean_object* v_mvarId_2332_; lean_object* v___y_2334_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_mvarId_2332_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_mvarId_2332_);
lean_dec_ref_known(v_x_2300_, 1);
v___x_2343_ = lean_unsigned_to_nat(1024u);
v___x_2344_ = lean_nat_dec_le(v___x_2343_, v_prec_2301_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2334_ = v___x_2345_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2334_ = v___x_2346_;
goto v___jp_2333_;
}
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2335_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__8));
v___x_2336_ = lean_unsigned_to_nat(1024u);
v___x_2337_ = l_Lean_Name_reprPrec(v_mvarId_2332_, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_inc(v___y_2334_);
v___x_2339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___y_2334_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = 0;
v___x_2341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2340_);
v___x_2342_ = l_Repr_addAppParen(v___x_2341_, v_prec_2301_);
return v___x_2342_;
}
}
case 3:
{
lean_object* v_u_2347_; lean_object* v___y_2349_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v_u_2347_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_u_2347_);
lean_dec_ref_known(v_x_2300_, 1);
v___x_2358_ = lean_unsigned_to_nat(1024u);
v___x_2359_ = lean_nat_dec_le(v___x_2358_, v_prec_2301_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2349_ = v___x_2360_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2349_ = v___x_2361_;
goto v___jp_2348_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2350_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__11));
v___x_2351_ = lean_unsigned_to_nat(1024u);
v___x_2352_ = l_Lean_instReprLevel_repr(v_u_2347_, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
lean_inc(v___y_2349_);
v___x_2354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___y_2349_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = 0;
v___x_2356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*1, v___x_2355_);
v___x_2357_ = l_Repr_addAppParen(v___x_2356_, v_prec_2301_);
return v___x_2357_;
}
}
case 4:
{
lean_object* v_declName_2362_; lean_object* v_us_2363_; lean_object* v___y_2365_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_declName_2362_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_declName_2362_);
v_us_2363_ = lean_ctor_get(v_x_2300_, 1);
lean_inc(v_us_2363_);
lean_dec_ref_known(v_x_2300_, 2);
v___x_2378_ = lean_unsigned_to_nat(1024u);
v___x_2379_ = lean_nat_dec_le(v___x_2378_, v_prec_2301_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2365_ = v___x_2380_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2365_ = v___x_2381_;
goto v___jp_2364_;
}
v___jp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2366_ = lean_box(1);
v___x_2367_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__14));
v___x_2368_ = lean_unsigned_to_nat(1024u);
v___x_2369_ = l_Lean_Name_reprPrec(v_declName_2362_, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2367_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2366_);
v___x_2372_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_us_2363_);
v___x_2373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
lean_inc(v___y_2365_);
v___x_2374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2365_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = 0;
v___x_2376_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*1, v___x_2375_);
v___x_2377_ = l_Repr_addAppParen(v___x_2376_, v_prec_2301_);
return v___x_2377_;
}
}
case 5:
{
lean_object* v_fn_2382_; lean_object* v_arg_2383_; lean_object* v___x_2384_; lean_object* v___y_2386_; uint8_t v___x_2398_; 
v_fn_2382_ = lean_ctor_get(v_x_2300_, 0);
lean_inc_ref(v_fn_2382_);
v_arg_2383_ = lean_ctor_get(v_x_2300_, 1);
lean_inc_ref(v_arg_2383_);
lean_dec_ref_known(v_x_2300_, 2);
v___x_2384_ = lean_unsigned_to_nat(1024u);
v___x_2398_ = lean_nat_dec_le(v___x_2384_, v_prec_2301_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2386_ = v___x_2399_;
goto v___jp_2385_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2386_ = v___x_2400_;
goto v___jp_2385_;
}
v___jp_2385_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2387_ = lean_box(1);
v___x_2388_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__17));
v___x_2389_ = l_Lean_instReprExpr_repr(v_fn_2382_, v___x_2384_);
v___x_2390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___x_2387_);
v___x_2392_ = l_Lean_instReprExpr_repr(v_arg_2383_, v___x_2384_);
v___x_2393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_inc(v___y_2386_);
v___x_2394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2386_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = 0;
v___x_2396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*1, v___x_2395_);
v___x_2397_ = l_Repr_addAppParen(v___x_2396_, v_prec_2301_);
return v___x_2397_;
}
}
case 6:
{
lean_object* v_binderName_2401_; lean_object* v_binderType_2402_; lean_object* v_body_2403_; uint8_t v_binderInfo_2404_; lean_object* v___x_2405_; lean_object* v___y_2407_; uint8_t v___x_2425_; 
v_binderName_2401_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_binderName_2401_);
v_binderType_2402_ = lean_ctor_get(v_x_2300_, 1);
lean_inc_ref(v_binderType_2402_);
v_body_2403_ = lean_ctor_get(v_x_2300_, 2);
lean_inc_ref(v_body_2403_);
v_binderInfo_2404_ = lean_ctor_get_uint8(v_x_2300_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2300_, 3);
v___x_2405_ = lean_unsigned_to_nat(1024u);
v___x_2425_ = lean_nat_dec_le(v___x_2405_, v_prec_2301_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2407_ = v___x_2426_;
goto v___jp_2406_;
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2407_ = v___x_2427_;
goto v___jp_2406_;
}
v___jp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2408_ = lean_box(1);
v___x_2409_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__20));
v___x_2410_ = l_Lean_Name_reprPrec(v_binderName_2401_, v___x_2405_);
v___x_2411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v___x_2408_);
v___x_2413_ = l_Lean_instReprExpr_repr(v_binderType_2402_, v___x_2405_);
v___x_2414_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2408_);
v___x_2416_ = l_Lean_instReprExpr_repr(v_body_2403_, v___x_2405_);
v___x_2417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2408_);
v___x_2419_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2404_, v___x_2405_);
v___x_2420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
lean_inc(v___y_2407_);
v___x_2421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___y_2407_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = 0;
v___x_2423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*1, v___x_2422_);
v___x_2424_ = l_Repr_addAppParen(v___x_2423_, v_prec_2301_);
return v___x_2424_;
}
}
case 7:
{
lean_object* v_binderName_2428_; lean_object* v_binderType_2429_; lean_object* v_body_2430_; uint8_t v_binderInfo_2431_; lean_object* v___x_2432_; lean_object* v___y_2434_; uint8_t v___x_2452_; 
v_binderName_2428_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_binderName_2428_);
v_binderType_2429_ = lean_ctor_get(v_x_2300_, 1);
lean_inc_ref(v_binderType_2429_);
v_body_2430_ = lean_ctor_get(v_x_2300_, 2);
lean_inc_ref(v_body_2430_);
v_binderInfo_2431_ = lean_ctor_get_uint8(v_x_2300_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_2300_, 3);
v___x_2432_ = lean_unsigned_to_nat(1024u);
v___x_2452_ = lean_nat_dec_le(v___x_2432_, v_prec_2301_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2434_ = v___x_2453_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2434_ = v___x_2454_;
goto v___jp_2433_;
}
v___jp_2433_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2435_ = lean_box(1);
v___x_2436_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__23));
v___x_2437_ = l_Lean_Name_reprPrec(v_binderName_2428_, v___x_2432_);
v___x_2438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2435_);
v___x_2440_ = l_Lean_instReprExpr_repr(v_binderType_2429_, v___x_2432_);
v___x_2441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
lean_ctor_set(v___x_2442_, 1, v___x_2435_);
v___x_2443_ = l_Lean_instReprExpr_repr(v_body_2430_, v___x_2432_);
v___x_2444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___x_2435_);
v___x_2446_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_2431_, v___x_2432_);
v___x_2447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
lean_inc(v___y_2434_);
v___x_2448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2434_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = 0;
v___x_2450_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1, v___x_2449_);
v___x_2451_ = l_Repr_addAppParen(v___x_2450_, v_prec_2301_);
return v___x_2451_;
}
}
case 8:
{
lean_object* v_declName_2455_; lean_object* v_type_2456_; lean_object* v_value_2457_; lean_object* v_body_2458_; uint8_t v_nondep_2459_; lean_object* v___x_2460_; lean_object* v___y_2462_; uint8_t v___x_2483_; 
v_declName_2455_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_declName_2455_);
v_type_2456_ = lean_ctor_get(v_x_2300_, 1);
lean_inc_ref(v_type_2456_);
v_value_2457_ = lean_ctor_get(v_x_2300_, 2);
lean_inc_ref(v_value_2457_);
v_body_2458_ = lean_ctor_get(v_x_2300_, 3);
lean_inc_ref(v_body_2458_);
v_nondep_2459_ = lean_ctor_get_uint8(v_x_2300_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_x_2300_, 4);
v___x_2460_ = lean_unsigned_to_nat(1024u);
v___x_2483_ = lean_nat_dec_le(v___x_2460_, v_prec_2301_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2462_ = v___x_2484_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2462_ = v___x_2485_;
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2463_ = lean_box(1);
v___x_2464_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__26));
v___x_2465_ = l_Lean_Name_reprPrec(v_declName_2455_, v___x_2460_);
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2463_);
v___x_2468_ = l_Lean_instReprExpr_repr(v_type_2456_, v___x_2460_);
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2463_);
v___x_2471_ = l_Lean_instReprExpr_repr(v_value_2457_, v___x_2460_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2463_);
v___x_2474_ = l_Lean_instReprExpr_repr(v_body_2458_, v___x_2460_);
v___x_2475_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2463_);
v___x_2477_ = l_Bool_repr___redArg(v_nondep_2459_);
v___x_2478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
lean_inc(v___y_2462_);
v___x_2479_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2462_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = 0;
v___x_2481_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*1, v___x_2480_);
v___x_2482_ = l_Repr_addAppParen(v___x_2481_, v_prec_2301_);
return v___x_2482_;
}
}
case 9:
{
lean_object* v_a_2486_; lean_object* v___y_2488_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v_a_2486_ = lean_ctor_get(v_x_2300_, 0);
lean_inc_ref(v_a_2486_);
lean_dec_ref_known(v_x_2300_, 1);
v___x_2497_ = lean_unsigned_to_nat(1024u);
v___x_2498_ = lean_nat_dec_le(v___x_2497_, v_prec_2301_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2488_ = v___x_2499_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2488_ = v___x_2500_;
goto v___jp_2487_;
}
v___jp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2489_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__29));
v___x_2490_ = lean_unsigned_to_nat(1024u);
v___x_2491_ = l_Lean_instReprLiteral_repr(v_a_2486_, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2489_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
lean_inc(v___y_2488_);
v___x_2493_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2488_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = 0;
v___x_2495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*1, v___x_2494_);
v___x_2496_ = l_Repr_addAppParen(v___x_2495_, v_prec_2301_);
return v___x_2496_;
}
}
case 10:
{
lean_object* v_data_2501_; lean_object* v_expr_2502_; lean_object* v___x_2503_; lean_object* v___y_2505_; uint8_t v___x_2517_; 
v_data_2501_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_data_2501_);
v_expr_2502_ = lean_ctor_get(v_x_2300_, 1);
lean_inc_ref(v_expr_2502_);
lean_dec_ref_known(v_x_2300_, 2);
v___x_2503_ = lean_unsigned_to_nat(1024u);
v___x_2517_ = lean_nat_dec_le(v___x_2503_, v_prec_2301_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2505_ = v___x_2518_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2505_ = v___x_2519_;
goto v___jp_2504_;
}
v___jp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2506_ = lean_box(1);
v___x_2507_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__32));
v___x_2508_ = l_Lean_instReprKVMap_repr___redArg(v_data_2501_);
v___x_2509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2506_);
v___x_2511_ = l_Lean_instReprExpr_repr(v_expr_2502_, v___x_2503_);
v___x_2512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_inc(v___y_2505_);
v___x_2513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2505_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*1, v___x_2514_);
v___x_2516_ = l_Repr_addAppParen(v___x_2515_, v_prec_2301_);
return v___x_2516_;
}
}
default: 
{
lean_object* v_typeName_2520_; lean_object* v_idx_2521_; lean_object* v_struct_2522_; lean_object* v___x_2523_; lean_object* v___y_2525_; uint8_t v___x_2541_; 
v_typeName_2520_ = lean_ctor_get(v_x_2300_, 0);
lean_inc(v_typeName_2520_);
v_idx_2521_ = lean_ctor_get(v_x_2300_, 1);
lean_inc(v_idx_2521_);
v_struct_2522_ = lean_ctor_get(v_x_2300_, 2);
lean_inc_ref(v_struct_2522_);
lean_dec_ref_known(v_x_2300_, 3);
v___x_2523_ = lean_unsigned_to_nat(1024u);
v___x_2541_ = lean_nat_dec_le(v___x_2523_, v_prec_2301_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__3, &l_Lean_instReprLiteral_repr___closed__3_once, _init_l_Lean_instReprLiteral_repr___closed__3);
v___y_2525_ = v___x_2542_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_obj_once(&l_Lean_instReprLiteral_repr___closed__4, &l_Lean_instReprLiteral_repr___closed__4_once, _init_l_Lean_instReprLiteral_repr___closed__4);
v___y_2525_ = v___x_2543_;
goto v___jp_2524_;
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2526_ = lean_box(1);
v___x_2527_ = ((lean_object*)(l_Lean_instReprExpr_repr___closed__35));
v___x_2528_ = l_Lean_Name_reprPrec(v_typeName_2520_, v___x_2523_);
v___x_2529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2526_);
v___x_2531_ = l_Nat_reprFast(v_idx_2521_);
v___x_2532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
v___x_2533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2530_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___x_2526_);
v___x_2535_ = l_Lean_instReprExpr_repr(v_struct_2522_, v___x_2523_);
v___x_2536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
lean_inc(v___y_2525_);
v___x_2537_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2525_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = 0;
v___x_2539_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*1, v___x_2538_);
v___x_2540_ = l_Repr_addAppParen(v___x_2539_, v_prec_2301_);
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprExpr_repr___boxed(lean_object* v_x_2544_, lean_object* v_prec_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_instReprExpr_repr(v_x_2544_, v_prec_2545_);
lean_dec(v_prec_2545_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_instReprExpr_repr_spec__0_spec__1(lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_nat_to_int(v_a_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0(lean_object* v_a_2549_, lean_object* v_n_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0___redArg(v_a_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprExpr_repr_spec__0___boxed(lean_object* v_a_2552_, lean_object* v_n_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_List_repr___at___00Lean_instReprExpr_repr_spec__0(v_a_2552_, v_n_2553_);
lean_dec(v_n_2553_);
return v_res_2554_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_box(0);
v___x_2561_ = ((lean_object*)(l_Lean_instInhabitedExpr___closed__1));
v___x_2562_ = l_Lean_Expr_const___override(v___x_2561_, v___x_2560_);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr(void){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* v_x_2576_){
_start:
{
switch(lean_obj_tag(v_x_2576_))
{
case 0:
{
lean_object* v___x_2577_; 
v___x_2577_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__0));
return v___x_2577_;
}
case 1:
{
lean_object* v___x_2578_; 
v___x_2578_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__1));
return v___x_2578_;
}
case 2:
{
lean_object* v___x_2579_; 
v___x_2579_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__2));
return v___x_2579_;
}
case 3:
{
lean_object* v___x_2580_; 
v___x_2580_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__3));
return v___x_2580_;
}
case 4:
{
lean_object* v___x_2581_; 
v___x_2581_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__4));
return v___x_2581_;
}
case 5:
{
lean_object* v___x_2582_; 
v___x_2582_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__5));
return v___x_2582_;
}
case 6:
{
lean_object* v___x_2583_; 
v___x_2583_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__6));
return v___x_2583_;
}
case 7:
{
lean_object* v___x_2584_; 
v___x_2584_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__7));
return v___x_2584_;
}
case 8:
{
lean_object* v___x_2585_; 
v___x_2585_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__8));
return v___x_2585_;
}
case 9:
{
lean_object* v___x_2586_; 
v___x_2586_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__9));
return v___x_2586_;
}
case 10:
{
lean_object* v___x_2587_; 
v___x_2587_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__10));
return v___x_2587_;
}
default: 
{
lean_object* v___x_2588_; 
v___x_2588_ = ((lean_object*)(l_Lean_Expr_ctorName___closed__11));
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* v_x_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Expr_ctorName(v_x_2589_);
lean_dec_ref(v_x_2589_);
return v_res_2590_;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* v_e_2591_){
_start:
{
uint64_t v___x_2592_; uint64_t v___x_2593_; 
v___x_2592_ = lean_expr_data(v_e_2591_);
v___x_2593_ = l_Lean_Expr_Data_hash(v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* v_e_2594_){
_start:
{
uint64_t v_res_2595_; lean_object* v_r_2596_; 
v_res_2595_ = l_Lean_Expr_hash(v_e_2594_);
lean_dec_ref(v_e_2594_);
v_r_2596_ = lean_box_uint64(v_res_2595_);
return v_r_2596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* v_e_2599_){
_start:
{
uint64_t v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = lean_expr_data(v_e_2599_);
v___x_2601_ = l_Lean_Expr_Data_hasFVar(v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* v_e_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = l_Lean_Expr_hasFVar(v_e_2602_);
lean_dec_ref(v_e_2602_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* v_e_2605_){
_start:
{
uint64_t v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = lean_expr_data(v_e_2605_);
v___x_2607_ = l_Lean_Expr_Data_hasExprMVar(v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* v_e_2608_){
_start:
{
uint8_t v_res_2609_; lean_object* v_r_2610_; 
v_res_2609_ = l_Lean_Expr_hasExprMVar(v_e_2608_);
lean_dec_ref(v_e_2608_);
v_r_2610_ = lean_box(v_res_2609_);
return v_r_2610_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* v_e_2611_){
_start:
{
uint64_t v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_expr_data(v_e_2611_);
v___x_2613_ = l_Lean_Expr_Data_hasLevelMVar(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* v_e_2614_){
_start:
{
uint8_t v_res_2615_; lean_object* v_r_2616_; 
v_res_2615_ = l_Lean_Expr_hasLevelMVar(v_e_2614_);
lean_dec_ref(v_e_2614_);
v_r_2616_ = lean_box(v_res_2615_);
return v_r_2616_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* v_e_2617_){
_start:
{
uint64_t v_d_2618_; uint8_t v___x_2619_; 
v_d_2618_ = lean_expr_data(v_e_2617_);
v___x_2619_ = l_Lean_Expr_Data_hasExprMVar(v_d_2618_);
if (v___x_2619_ == 0)
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Lean_Expr_Data_hasLevelMVar(v_d_2618_);
return v___x_2620_;
}
else
{
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* v_e_2621_){
_start:
{
uint8_t v_res_2622_; lean_object* v_r_2623_; 
v_res_2622_ = l_Lean_Expr_hasMVar(v_e_2621_);
lean_dec_ref(v_e_2621_);
v_r_2623_ = lean_box(v_res_2622_);
return v_r_2623_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* v_e_2624_){
_start:
{
uint64_t v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = lean_expr_data(v_e_2624_);
v___x_2626_ = l_Lean_Expr_Data_hasLevelParam(v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* v_e_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Lean_Expr_hasLevelParam(v_e_2627_);
lean_dec_ref(v_e_2627_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* v_e_2630_){
_start:
{
uint64_t v___x_2631_; uint8_t v___x_2632_; uint32_t v___x_2633_; 
v___x_2631_ = lean_expr_data(v_e_2630_);
v___x_2632_ = l_Lean_Expr_Data_approxDepth(v___x_2631_);
v___x_2633_ = lean_uint8_to_uint32(v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* v_e_2634_){
_start:
{
uint32_t v_res_2635_; lean_object* v_r_2636_; 
v_res_2635_ = l_Lean_Expr_approxDepth(v_e_2634_);
lean_dec_ref(v_e_2634_);
v_r_2636_ = lean_box_uint32(v_res_2635_);
return v_r_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* v_e_2637_){
_start:
{
uint64_t v___x_2638_; uint32_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_expr_data(v_e_2637_);
v___x_2639_ = l_Lean_Expr_Data_looseBVarRange(v___x_2638_);
v___x_2640_ = lean_uint32_to_nat(v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* v_e_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Expr_looseBVarRange(v_e_2641_);
lean_dec_ref(v_e_2641_);
return v_res_2642_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* v_e_2643_){
_start:
{
switch(lean_obj_tag(v_e_2643_))
{
case 7:
{
uint8_t v_binderInfo_2644_; 
v_binderInfo_2644_ = lean_ctor_get_uint8(v_e_2643_, sizeof(void*)*3 + 8);
return v_binderInfo_2644_;
}
case 6:
{
uint8_t v_binderInfo_2645_; 
v_binderInfo_2645_ = lean_ctor_get_uint8(v_e_2643_, sizeof(void*)*3 + 8);
return v_binderInfo_2645_;
}
default: 
{
uint8_t v___x_2646_; 
v___x_2646_ = 0;
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* v_e_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_Lean_Expr_binderInfo(v_e_2647_);
lean_dec_ref(v_e_2647_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* v_a_2650_){
_start:
{
uint64_t v___x_2651_; 
v___x_2651_ = l_Lean_Expr_hash(v_a_2650_);
lean_dec_ref(v_a_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* v_a_2652_){
_start:
{
uint64_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = lean_expr_hash(v_a_2652_);
v_r_2654_ = lean_box_uint64(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* v_e_2655_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = l_Lean_Expr_hasFVar(v_e_2655_);
lean_dec_ref(v_e_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* v_e_2657_){
_start:
{
uint8_t v_res_2658_; lean_object* v_r_2659_; 
v_res_2658_ = lean_expr_has_fvar(v_e_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* v_e_2660_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_Expr_hasExprMVar(v_e_2660_);
lean_dec_ref(v_e_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* v_e_2662_){
_start:
{
uint8_t v_res_2663_; lean_object* v_r_2664_; 
v_res_2663_ = lean_expr_has_expr_mvar(v_e_2662_);
v_r_2664_ = lean_box(v_res_2663_);
return v_r_2664_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* v_e_2665_){
_start:
{
uint8_t v___x_2666_; 
v___x_2666_ = l_Lean_Expr_hasLevelMVar(v_e_2665_);
lean_dec_ref(v_e_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* v_e_2667_){
_start:
{
uint8_t v_res_2668_; lean_object* v_r_2669_; 
v_res_2668_ = lean_expr_has_level_mvar(v_e_2667_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* v_e_2670_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_Expr_hasLevelParam(v_e_2670_);
lean_dec_ref(v_e_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* v_e_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = lean_expr_has_level_param(v_e_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* v_e_2675_){
_start:
{
uint64_t v___x_2676_; uint32_t v___x_2677_; 
v___x_2676_ = lean_expr_data(v_e_2675_);
lean_dec_ref(v_e_2675_);
v___x_2677_ = l_Lean_Expr_Data_looseBVarRange(v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* v_e_2678_){
_start:
{
uint32_t v_res_2679_; lean_object* v_r_2680_; 
v_res_2679_ = lean_expr_loose_bvar_range(v_e_2678_);
v_r_2680_ = lean_box_uint32(v_res_2679_);
return v_r_2680_;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* v_e_2681_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = l_Lean_Expr_binderInfo(v_e_2681_);
lean_dec_ref(v_e_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* v_e_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = lean_expr_binder_info(v_e_2683_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* v_declName_2686_, lean_object* v_us_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_Expr_const___override(v_declName_2686_, v_us_2687_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = ((lean_object*)(l_Lean_Literal_type___closed__1));
v___x_2694_ = l_Lean_Expr_const___override(v___x_2693_, v___x_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_box(0);
v___x_2699_ = ((lean_object*)(l_Lean_Literal_type___closed__4));
v___x_2700_ = l_Lean_Expr_const___override(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* v_x_2701_){
_start:
{
if (lean_obj_tag(v_x_2701_) == 0)
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_2702_;
}
else
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_obj_once(&l_Lean_Literal_type___closed__5, &l_Lean_Literal_type___closed__5_once, _init_l_Lean_Literal_type___closed__5);
return v___x_2703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* v_x_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Literal_type(v_x_2704_);
lean_dec_ref(v_x_2704_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Literal_type(v_a_2706_);
lean_dec_ref(v_a_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* v_idx_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Expr_bvar___override(v_idx_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* v_u_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Expr_sort___override(v_u_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* v_fvarId_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_Expr_fvar___override(v_fvarId_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* v_mvarId_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_Expr_mvar___override(v_mvarId_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* v_m_2716_, lean_object* v_e_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Expr_mdata___override(v_m_2716_, v_e_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* v_structName_2719_, lean_object* v_idx_2720_, lean_object* v_struct_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Expr_proj___override(v_structName_2719_, v_idx_2720_, v_struct_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* v_f_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Expr_app___override(v_f_2723_, v_a_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* v_x_2726_, uint8_t v_bi_2727_, lean_object* v_t_2728_, lean_object* v_b_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Expr_lam___override(v_x_2726_, v_t_2728_, v_b_2729_, v_bi_2727_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* v_x_2731_, lean_object* v_bi_2732_, lean_object* v_t_2733_, lean_object* v_b_2734_){
_start:
{
uint8_t v_bi_boxed_2735_; lean_object* v_res_2736_; 
v_bi_boxed_2735_ = lean_unbox(v_bi_2732_);
v_res_2736_ = l_Lean_mkLambda(v_x_2731_, v_bi_boxed_2735_, v_t_2733_, v_b_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* v_x_2737_, uint8_t v_bi_2738_, lean_object* v_t_2739_, lean_object* v_b_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_Expr_forallE___override(v_x_2737_, v_t_2739_, v_b_2740_, v_bi_2738_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* v_x_2742_, lean_object* v_bi_2743_, lean_object* v_t_2744_, lean_object* v_b_2745_){
_start:
{
uint8_t v_bi_boxed_2746_; lean_object* v_res_2747_; 
v_bi_boxed_2746_ = lean_unbox(v_bi_2743_);
v_res_2747_ = l_Lean_mkForall(v_x_2742_, v_bi_boxed_2746_, v_t_2744_, v_b_2745_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__4(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__3));
v___x_2756_ = l_Lean_Expr_const___override(v___x_2755_, v___x_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* v_type_2757_){
_start:
{
lean_object* v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2759_ = 0;
v___x_2760_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2761_ = l_Lean_Expr_forallE___override(v___x_2758_, v___x_2760_, v_type_2757_, v___x_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* v_type_2762_){
_start:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = ((lean_object*)(l_Lean_mkSimpleThunkType___closed__1));
v___x_2764_ = 0;
v___x_2765_ = lean_obj_once(&l_Lean_mkSimpleThunkType___closed__4, &l_Lean_mkSimpleThunkType___closed__4_once, _init_l_Lean_mkSimpleThunkType___closed__4);
v___x_2766_ = l_Lean_Expr_lam___override(v___x_2763_, v___x_2765_, v_type_2762_, v___x_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* v_x_2767_, lean_object* v_t_2768_, lean_object* v_v_2769_, lean_object* v_b_2770_, uint8_t v_nondep_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Expr_letE___override(v_x_2767_, v_t_2768_, v_v_2769_, v_b_2770_, v_nondep_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* v_x_2773_, lean_object* v_t_2774_, lean_object* v_v_2775_, lean_object* v_b_2776_, lean_object* v_nondep_2777_){
_start:
{
uint8_t v_nondep_boxed_2778_; lean_object* v_res_2779_; 
v_nondep_boxed_2778_ = lean_unbox(v_nondep_2777_);
v_res_2779_ = l_Lean_mkLet(v_x_2773_, v_t_2774_, v_v_2775_, v_b_2776_, v_nondep_boxed_2778_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHave(lean_object* v_x_2780_, lean_object* v_t_2781_, lean_object* v_v_2782_, lean_object* v_b_2783_){
_start:
{
uint8_t v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = 1;
v___x_2785_ = l_Lean_Expr_letE___override(v_x_2780_, v_t_2781_, v_v_2782_, v_b_2783_, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* v_f_2786_, lean_object* v_a_2787_, lean_object* v_b_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = l_Lean_Expr_app___override(v_f_2786_, v_a_2787_);
v___x_2790_ = l_Lean_Expr_app___override(v___x_2789_, v_b_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* v_f_2791_, lean_object* v_a_2792_, lean_object* v_b_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Lean_mkAppB(v_f_2791_, v_a_2792_, v_b_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* v_f_2795_, lean_object* v_a_2796_, lean_object* v_b_2797_, lean_object* v_c_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = l_Lean_mkAppB(v_f_2795_, v_a_2796_, v_b_2797_);
v___x_2800_ = l_Lean_Expr_app___override(v___x_2799_, v_c_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* v_f_2801_, lean_object* v_a_2802_, lean_object* v_b_2803_, lean_object* v_c_2804_, lean_object* v_d_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = l_Lean_mkAppB(v_f_2801_, v_a_2802_, v_b_2803_);
v___x_2807_ = l_Lean_mkAppB(v___x_2806_, v_c_2804_, v_d_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* v_f_2808_, lean_object* v_a_2809_, lean_object* v_b_2810_, lean_object* v_c_2811_, lean_object* v_d_2812_, lean_object* v_e_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = l_Lean_mkApp4(v_f_2808_, v_a_2809_, v_b_2810_, v_c_2811_, v_d_2812_);
v___x_2815_ = l_Lean_Expr_app___override(v___x_2814_, v_e_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* v_f_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v_c_2819_, lean_object* v_d_2820_, lean_object* v_e_u2081_2821_, lean_object* v_e_u2082_2822_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = l_Lean_mkApp4(v_f_2816_, v_a_2817_, v_b_2818_, v_c_2819_, v_d_2820_);
v___x_2824_ = l_Lean_mkAppB(v___x_2823_, v_e_u2081_2821_, v_e_u2082_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* v_f_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_c_2828_, lean_object* v_d_2829_, lean_object* v_e_u2081_2830_, lean_object* v_e_u2082_2831_, lean_object* v_e_u2083_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = l_Lean_mkApp4(v_f_2825_, v_a_2826_, v_b_2827_, v_c_2828_, v_d_2829_);
v___x_2834_ = l_Lean_mkApp3(v___x_2833_, v_e_u2081_2830_, v_e_u2082_2831_, v_e_u2083_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* v_f_2835_, lean_object* v_a_2836_, lean_object* v_b_2837_, lean_object* v_c_2838_, lean_object* v_d_2839_, lean_object* v_e_u2081_2840_, lean_object* v_e_u2082_2841_, lean_object* v_e_u2083_2842_, lean_object* v_e_u2084_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = l_Lean_mkApp4(v_f_2835_, v_a_2836_, v_b_2837_, v_c_2838_, v_d_2839_);
v___x_2845_ = l_Lean_mkApp4(v___x_2844_, v_e_u2081_2840_, v_e_u2082_2841_, v_e_u2083_2842_, v_e_u2084_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* v_f_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_, lean_object* v_d_2850_, lean_object* v_e_u2081_2851_, lean_object* v_e_u2082_2852_, lean_object* v_e_u2083_2853_, lean_object* v_e_u2084_2854_, lean_object* v_e_u2085_2855_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = l_Lean_mkApp4(v_f_2846_, v_a_2847_, v_b_2848_, v_c_2849_, v_d_2850_);
v___x_2857_ = l_Lean_mkApp5(v___x_2856_, v_e_u2081_2851_, v_e_u2082_2852_, v_e_u2083_2853_, v_e_u2084_2854_, v_e_u2085_2855_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* v_f_2858_, lean_object* v_a_2859_, lean_object* v_b_2860_, lean_object* v_c_2861_, lean_object* v_d_2862_, lean_object* v_e_u2081_2863_, lean_object* v_e_u2082_2864_, lean_object* v_e_u2083_2865_, lean_object* v_e_u2084_2866_, lean_object* v_e_u2085_2867_, lean_object* v_e_u2086_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = l_Lean_mkApp4(v_f_2858_, v_a_2859_, v_b_2860_, v_c_2861_, v_d_2862_);
v___x_2870_ = l_Lean_mkApp6(v___x_2869_, v_e_u2081_2863_, v_e_u2082_2864_, v_e_u2083_2865_, v_e_u2084_2866_, v_e_u2085_2867_, v_e_u2086_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* v_l_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Expr_lit___override(v_l_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* v_n_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_n_2873_);
v___x_2875_ = l_Lean_Expr_lit___override(v___x_2874_);
return v___x_2875_;
}
}
static lean_object* _init_l_Lean_mkInstOfNatNat___closed__2(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = ((lean_object*)(l_Lean_mkInstOfNatNat___closed__1));
v___x_2881_ = l_Lean_Expr_const___override(v___x_2880_, v___x_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInstOfNatNat(lean_object* v_n_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_obj_once(&l_Lean_mkInstOfNatNat___closed__2, &l_Lean_mkInstOfNatNat___closed__2_once, _init_l_Lean_mkInstOfNatNat___closed__2);
v___x_2884_ = l_Lean_Expr_app___override(v___x_2883_, v_n_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_mkNatLitCore___closed__4(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2893_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_2894_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_2895_ = l_Lean_Expr_const___override(v___x_2894_, v___x_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLitCore(lean_object* v_n_2896_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2897_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_2898_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
lean_inc_ref(v_n_2896_);
v___x_2899_ = l_Lean_mkInstOfNatNat(v_n_2896_);
v___x_2900_ = l_Lean_mkApp3(v___x_2897_, v___x_2898_, v_n_2896_, v___x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* v_n_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = l_Lean_mkRawNatLit(v_n_2901_);
v___x_2903_ = l_Lean_mkNatLitCore(v___x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* v_s_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_s_2904_);
v___x_2906_ = l_Lean_Expr_lit___override(v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* v_idx_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Expr_bvar___override(v_idx_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* v_fvarId_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_Expr_fvar___override(v_fvarId_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* v_u_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Expr_sort___override(v_u_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* v_c_2913_, lean_object* v_lvls_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_Expr_const___override(v_c_2913_, v_lvls_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* v_f_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_Expr_app___override(v_f_2916_, v_a_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* v_n_2919_, lean_object* v_d_2920_, lean_object* v_b_2921_, uint8_t v_bi_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Expr_lam___override(v_n_2919_, v_d_2920_, v_b_2921_, v_bi_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* v_n_2924_, lean_object* v_d_2925_, lean_object* v_b_2926_, lean_object* v_bi_2927_){
_start:
{
uint8_t v_bi_boxed_2928_; lean_object* v_res_2929_; 
v_bi_boxed_2928_ = lean_unbox(v_bi_2927_);
v_res_2929_ = lean_expr_mk_lambda(v_n_2924_, v_d_2925_, v_b_2926_, v_bi_boxed_2928_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* v_n_2930_, lean_object* v_d_2931_, lean_object* v_b_2932_, uint8_t v_bi_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Expr_forallE___override(v_n_2930_, v_d_2931_, v_b_2932_, v_bi_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* v_n_2935_, lean_object* v_d_2936_, lean_object* v_b_2937_, lean_object* v_bi_2938_){
_start:
{
uint8_t v_bi_boxed_2939_; lean_object* v_res_2940_; 
v_bi_boxed_2939_ = lean_unbox(v_bi_2938_);
v_res_2940_ = lean_expr_mk_forall(v_n_2935_, v_d_2936_, v_b_2937_, v_bi_boxed_2939_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* v_n_2941_, lean_object* v_t_2942_, lean_object* v_v_2943_, lean_object* v_b_2944_, uint8_t v_nondep_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_Expr_letE___override(v_n_2941_, v_t_2942_, v_v_2943_, v_b_2944_, v_nondep_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetEx___boxed(lean_object* v_n_2947_, lean_object* v_t_2948_, lean_object* v_v_2949_, lean_object* v_b_2950_, lean_object* v_nondep_2951_){
_start:
{
uint8_t v_nondep_boxed_2952_; lean_object* v_res_2953_; 
v_nondep_boxed_2952_ = lean_unbox(v_nondep_2951_);
v_res_2953_ = lean_expr_mk_let(v_n_2947_, v_t_2948_, v_v_2949_, v_b_2950_, v_nondep_boxed_2952_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* v_l_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Expr_lit___override(v_l_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* v_m_2956_, lean_object* v_e_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Expr_mdata___override(v_m_2956_, v_e_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* v_structName_2959_, lean_object* v_idx_2960_, lean_object* v_struct_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Expr_proj___override(v_structName_2959_, v_idx_2960_, v_struct_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(lean_object* v_as_2963_, size_t v_i_2964_, size_t v_stop_2965_, lean_object* v_b_2966_){
_start:
{
uint8_t v___x_2967_; 
v___x_2967_ = lean_usize_dec_eq(v_i_2964_, v_stop_2965_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; 
v___x_2968_ = lean_array_uget_borrowed(v_as_2963_, v_i_2964_);
lean_inc(v___x_2968_);
v___x_2969_ = l_Lean_Expr_app___override(v_b_2966_, v___x_2968_);
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2964_, v___x_2970_);
v_i_2964_ = v___x_2971_;
v_b_2966_ = v___x_2969_;
goto _start;
}
else
{
return v_b_2966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0___boxed(lean_object* v_as_2973_, lean_object* v_i_2974_, lean_object* v_stop_2975_, lean_object* v_b_2976_){
_start:
{
size_t v_i_boxed_2977_; size_t v_stop_boxed_2978_; lean_object* v_res_2979_; 
v_i_boxed_2977_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_stop_boxed_2978_ = lean_unbox_usize(v_stop_2975_);
lean_dec(v_stop_2975_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_as_2973_, v_i_boxed_2977_, v_stop_boxed_2978_, v_b_2976_);
lean_dec_ref(v_as_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* v_f_2980_, lean_object* v_args_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2982_ = lean_unsigned_to_nat(0u);
v___x_2983_ = lean_array_get_size(v_args_2981_);
v___x_2984_ = lean_nat_dec_lt(v___x_2982_, v___x_2983_);
if (v___x_2984_ == 0)
{
return v_f_2980_;
}
else
{
size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((size_t)0ULL);
v___x_2986_ = lean_usize_of_nat(v___x_2983_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkAppN_spec__0(v_args_2981_, v___x_2985_, v___x_2986_, v_f_2980_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppN___boxed(lean_object* v_f_2988_, lean_object* v_args_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_mkAppN(v_f_2988_, v_args_2989_);
lean_dec_ref(v_args_2989_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* v_n_2991_, lean_object* v_args_2992_, lean_object* v_i_2993_, lean_object* v_e_2994_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_nat_dec_lt(v_i_2993_, v_n_2991_);
if (v___x_2995_ == 0)
{
lean_dec(v_i_2993_);
return v_e_2994_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2996_ = l_Lean_instInhabitedExpr;
v___x_2997_ = lean_unsigned_to_nat(1u);
v___x_2998_ = lean_nat_add(v_i_2993_, v___x_2997_);
v___x_2999_ = lean_array_get_borrowed(v___x_2996_, v_args_2992_, v_i_2993_);
lean_dec(v_i_2993_);
lean_inc(v___x_2999_);
v___x_3000_ = l_Lean_Expr_app___override(v_e_2994_, v___x_2999_);
v_i_2993_ = v___x_2998_;
v_e_2994_ = v___x_3000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* v_n_3002_, lean_object* v_args_3003_, lean_object* v_i_3004_, lean_object* v_e_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_n_3002_, v_args_3003_, v_i_3004_, v_e_3005_);
lean_dec_ref(v_args_3003_);
lean_dec(v_n_3002_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* v_f_3007_, lean_object* v_i_3008_, lean_object* v_j_3009_, lean_object* v_args_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Lean_Expr_0__Lean_mkAppRangeAux(v_j_3009_, v_args_3010_, v_i_3008_, v_f_3007_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* v_f_3012_, lean_object* v_i_3013_, lean_object* v_j_3014_, lean_object* v_args_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_mkAppRange(v_f_3012_, v_i_3013_, v_j_3014_, v_args_3015_);
lean_dec_ref(v_args_3015_);
lean_dec(v_j_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(lean_object* v_as_3017_, size_t v_i_3018_, size_t v_stop_3019_, lean_object* v_b_3020_){
_start:
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_usize_dec_eq(v_i_3018_, v_stop_3019_);
if (v___x_3021_ == 0)
{
size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_sub(v_i_3018_, v___x_3022_);
v___x_3024_ = lean_array_uget_borrowed(v_as_3017_, v___x_3023_);
lean_inc(v___x_3024_);
v___x_3025_ = l_Lean_Expr_app___override(v_b_3020_, v___x_3024_);
v_i_3018_ = v___x_3023_;
v_b_3020_ = v___x_3025_;
goto _start;
}
else
{
return v_b_3020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0___boxed(lean_object* v_as_3027_, lean_object* v_i_3028_, lean_object* v_stop_3029_, lean_object* v_b_3030_){
_start:
{
size_t v_i_boxed_3031_; size_t v_stop_boxed_3032_; lean_object* v_res_3033_; 
v_i_boxed_3031_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_stop_boxed_3032_ = lean_unbox_usize(v_stop_3029_);
lean_dec(v_stop_3029_);
v_res_3033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_as_3027_, v_i_boxed_3031_, v_stop_boxed_3032_, v_b_3030_);
lean_dec_ref(v_as_3027_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* v_fn_3034_, lean_object* v_revArgs_3035_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3036_ = lean_array_get_size(v_revArgs_3035_);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = lean_nat_dec_lt(v___x_3037_, v___x_3036_);
if (v___x_3038_ == 0)
{
return v_fn_3034_;
}
else
{
size_t v___x_3039_; size_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_usize_of_nat(v___x_3036_);
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_mkAppRev_spec__0(v_revArgs_3035_, v___x_3039_, v___x_3040_, v_fn_3034_);
return v___x_3041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRev___boxed(lean_object* v_fn_3042_, lean_object* v_revArgs_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_mkAppRev(v_fn_3042_, v_revArgs_3043_);
lean_dec_ref(v_revArgs_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* v_e_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = lean_expr_dbg_to_string(v_e_3046_);
lean_dec_ref(v_e_3046_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* v_a_3050_, lean_object* v_b_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = lean_expr_quick_lt(v_a_3050_, v_b_3051_);
lean_dec_ref(v_b_3051_);
lean_dec_ref(v_a_3050_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* v_a_3056_, lean_object* v_b_3057_){
_start:
{
uint8_t v_res_3058_; lean_object* v_r_3059_; 
v_res_3058_ = lean_expr_lt(v_a_3056_, v_b_3057_);
lean_dec_ref(v_b_3057_);
lean_dec_ref(v_a_3056_);
v_r_3059_ = lean_box(v_res_3058_);
return v_r_3059_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_quickComp(lean_object* v_a_3060_, lean_object* v_b_3061_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_expr_quick_lt(v_a_3060_, v_b_3061_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_expr_quick_lt(v_b_3061_, v_a_3060_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = 1;
return v___x_3064_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = 2;
return v___x_3065_;
}
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = 0;
return v___x_3066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickComp___boxed(lean_object* v_a_3067_, lean_object* v_b_3068_){
_start:
{
uint8_t v_res_3069_; lean_object* v_r_3070_; 
v_res_3069_ = l_Lean_Expr_quickComp(v_a_3067_, v_b_3068_);
lean_dec_ref(v_b_3068_);
lean_dec_ref(v_a_3067_);
v_r_3070_ = lean_box(v_res_3069_);
return v_r_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* v_a_3073_, lean_object* v_b_3074_){
_start:
{
uint8_t v_res_3075_; lean_object* v_r_3076_; 
v_res_3075_ = lean_expr_eqv(v_a_3073_, v_b_3074_);
lean_dec_ref(v_b_3074_);
lean_dec_ref(v_a_3073_);
v_r_3076_ = lean_box(v_res_3075_);
return v_r_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* v_a_3081_, lean_object* v_b_3082_){
_start:
{
uint8_t v_res_3083_; lean_object* v_r_3084_; 
v_res_3083_ = lean_expr_equal(v_a_3081_, v_b_3082_);
lean_dec_ref(v_b_3082_);
lean_dec_ref(v_a_3081_);
v_r_3084_ = lean_box(v_res_3083_);
return v_r_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eqvBudgeted___boxed(lean_object* v_a_3089_, lean_object* v_b_3090_, lean_object* v_budget_3091_, lean_object* v_a_00___x40___internal___hyg_3092_){
_start:
{
size_t v_budget_boxed_3093_; uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_budget_boxed_3093_ = lean_unbox_usize(v_budget_3091_);
lean_dec(v_budget_3091_);
v_res_3094_ = lean_expr_eqv_budgeted(v_a_3089_, v_b_3090_, v_budget_boxed_3093_);
lean_dec_ref(v_b_3090_);
lean_dec_ref(v_a_3089_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_equalBudgeted___boxed(lean_object* v_a_3100_, lean_object* v_b_3101_, lean_object* v_budget_3102_, lean_object* v_a_00___x40___internal___hyg_3103_){
_start:
{
size_t v_budget_boxed_3104_; uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_budget_boxed_3104_ = lean_unbox_usize(v_budget_3102_);
lean_dec(v_budget_3102_);
v_res_3105_ = lean_expr_equal_budgeted(v_a_3100_, v_b_3101_, v_budget_boxed_3104_);
lean_dec_ref(v_b_3101_);
lean_dec_ref(v_a_3100_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* v_x_3107_){
_start:
{
if (lean_obj_tag(v_x_3107_) == 3)
{
uint8_t v___x_3108_; 
v___x_3108_ = 1;
return v___x_3108_;
}
else
{
uint8_t v___x_3109_; 
v___x_3109_ = 0;
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* v_x_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_Lean_Expr_isSort(v_x_3110_);
lean_dec_ref(v_x_3110_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 3)
{
lean_object* v_u_3114_; 
v_u_3114_ = lean_ctor_get(v_x_3113_, 0);
if (lean_obj_tag(v_u_3114_) == 1)
{
uint8_t v___x_3115_; 
v___x_3115_ = 1;
return v___x_3115_;
}
else
{
uint8_t v___x_3116_; 
v___x_3116_ = 0;
return v___x_3116_;
}
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = 0;
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* v_x_3118_){
_start:
{
uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_res_3119_ = l_Lean_Expr_isType(v_x_3118_);
lean_dec_ref(v_x_3118_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isType0(lean_object* v_x_3121_){
_start:
{
if (lean_obj_tag(v_x_3121_) == 3)
{
lean_object* v_u_3122_; 
v_u_3122_ = lean_ctor_get(v_x_3121_, 0);
if (lean_obj_tag(v_u_3122_) == 1)
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v_u_3122_, 0);
if (lean_obj_tag(v_a_3123_) == 0)
{
uint8_t v___x_3124_; 
v___x_3124_ = 1;
return v___x_3124_;
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = 0;
return v___x_3125_;
}
}
else
{
uint8_t v___x_3126_; 
v___x_3126_ = 0;
return v___x_3126_;
}
}
else
{
uint8_t v___x_3127_; 
v___x_3127_ = 0;
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isType0___boxed(lean_object* v_x_3128_){
_start:
{
uint8_t v_res_3129_; lean_object* v_r_3130_; 
v_res_3129_ = l_Lean_Expr_isType0(v_x_3128_);
lean_dec_ref(v_x_3128_);
v_r_3130_ = lean_box(v_res_3129_);
return v_r_3130_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* v_x_3131_){
_start:
{
if (lean_obj_tag(v_x_3131_) == 3)
{
lean_object* v_u_3132_; 
v_u_3132_ = lean_ctor_get(v_x_3131_, 0);
if (lean_obj_tag(v_u_3132_) == 0)
{
uint8_t v___x_3133_; 
v___x_3133_ = 1;
return v___x_3133_;
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = 0;
return v___x_3134_;
}
}
else
{
uint8_t v___x_3135_; 
v___x_3135_ = 0;
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* v_x_3136_){
_start:
{
uint8_t v_res_3137_; lean_object* v_r_3138_; 
v_res_3137_ = l_Lean_Expr_isProp(v_x_3136_);
lean_dec_ref(v_x_3136_);
v_r_3138_ = lean_box(v_res_3137_);
return v_r_3138_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
uint8_t v___x_3140_; 
v___x_3140_ = 1;
return v___x_3140_;
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = 0;
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* v_x_3142_){
_start:
{
uint8_t v_res_3143_; lean_object* v_r_3144_; 
v_res_3143_ = l_Lean_Expr_isBVar(v_x_3142_);
lean_dec_ref(v_x_3142_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* v_x_3145_){
_start:
{
if (lean_obj_tag(v_x_3145_) == 2)
{
uint8_t v___x_3146_; 
v___x_3146_ = 1;
return v___x_3146_;
}
else
{
uint8_t v___x_3147_; 
v___x_3147_ = 0;
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* v_x_3148_){
_start:
{
uint8_t v_res_3149_; lean_object* v_r_3150_; 
v_res_3149_ = l_Lean_Expr_isMVar(v_x_3148_);
lean_dec_ref(v_x_3148_);
v_r_3150_ = lean_box(v_res_3149_);
return v_r_3150_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* v_x_3151_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 1)
{
uint8_t v___x_3152_; 
v___x_3152_ = 1;
return v___x_3152_;
}
else
{
uint8_t v___x_3153_; 
v___x_3153_ = 0;
return v___x_3153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* v_x_3154_){
_start:
{
uint8_t v_res_3155_; lean_object* v_r_3156_; 
v_res_3155_ = l_Lean_Expr_isFVar(v_x_3154_);
lean_dec_ref(v_x_3154_);
v_r_3156_ = lean_box(v_res_3155_);
return v_r_3156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* v_x_3157_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 5)
{
uint8_t v___x_3158_; 
v___x_3158_ = 1;
return v___x_3158_;
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = 0;
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* v_x_3160_){
_start:
{
uint8_t v_res_3161_; lean_object* v_r_3162_; 
v_res_3161_ = l_Lean_Expr_isApp(v_x_3160_);
lean_dec_ref(v_x_3160_);
v_r_3162_ = lean_box(v_res_3161_);
return v_r_3162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* v_x_3163_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 11)
{
uint8_t v___x_3164_; 
v___x_3164_ = 1;
return v___x_3164_;
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 0;
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* v_x_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Lean_Expr_isProj(v_x_3166_);
lean_dec_ref(v_x_3166_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* v_x_3169_){
_start:
{
if (lean_obj_tag(v_x_3169_) == 4)
{
uint8_t v___x_3170_; 
v___x_3170_ = 1;
return v___x_3170_;
}
else
{
uint8_t v___x_3171_; 
v___x_3171_ = 0;
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* v_x_3172_){
_start:
{
uint8_t v_res_3173_; lean_object* v_r_3174_; 
v_res_3173_ = l_Lean_Expr_isConst(v_x_3172_);
lean_dec_ref(v_x_3172_);
v_r_3174_ = lean_box(v_res_3173_);
return v_r_3174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3175_) == 4)
{
lean_object* v_declName_3177_; uint8_t v___x_3178_; 
v_declName_3177_ = lean_ctor_get(v_x_3175_, 0);
v___x_3178_ = lean_name_eq(v_declName_3177_, v_x_3176_);
return v___x_3178_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = 0;
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_Expr_isConstOf(v_x_3180_, v_x_3181_);
lean_dec(v_x_3181_);
lean_dec_ref(v_x_3180_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVarOf(lean_object* v_x_3184_, lean_object* v_x_3185_){
_start:
{
if (lean_obj_tag(v_x_3184_) == 1)
{
lean_object* v_fvarId_3186_; uint8_t v___x_3187_; 
v_fvarId_3186_ = lean_ctor_get(v_x_3184_, 0);
v___x_3187_ = lean_name_eq(v_fvarId_3186_, v_x_3185_);
return v___x_3187_;
}
else
{
uint8_t v___x_3188_; 
v___x_3188_ = 0;
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFVarOf___boxed(lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Lean_Expr_isFVarOf(v_x_3189_, v_x_3190_);
lean_dec(v_x_3190_);
lean_dec_ref(v_x_3189_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* v_x_3193_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 7)
{
uint8_t v___x_3194_; 
v___x_3194_ = 1;
return v___x_3194_;
}
else
{
uint8_t v___x_3195_; 
v___x_3195_ = 0;
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* v_x_3196_){
_start:
{
uint8_t v_res_3197_; lean_object* v_r_3198_; 
v_res_3197_ = l_Lean_Expr_isForall(v_x_3196_);
lean_dec_ref(v_x_3196_);
v_r_3198_ = lean_box(v_res_3197_);
return v_r_3198_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* v_x_3199_){
_start:
{
if (lean_obj_tag(v_x_3199_) == 6)
{
uint8_t v___x_3200_; 
v___x_3200_ = 1;
return v___x_3200_;
}
else
{
uint8_t v___x_3201_; 
v___x_3201_ = 0;
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* v_x_3202_){
_start:
{
uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_res_3203_ = l_Lean_Expr_isLambda(v_x_3202_);
lean_dec_ref(v_x_3202_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* v_x_3205_){
_start:
{
switch(lean_obj_tag(v_x_3205_))
{
case 6:
{
uint8_t v___x_3206_; 
v___x_3206_ = 1;
return v___x_3206_;
}
case 7:
{
uint8_t v___x_3207_; 
v___x_3207_ = 1;
return v___x_3207_;
}
default: 
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
return v___x_3208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* v_x_3209_){
_start:
{
uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_res_3210_ = l_Lean_Expr_isBinding(v_x_3209_);
lean_dec_ref(v_x_3209_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3212_) == 8)
{
uint8_t v___x_3213_; 
v___x_3213_ = 1;
return v___x_3213_;
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = 0;
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* v_x_3215_){
_start:
{
uint8_t v_res_3216_; lean_object* v_r_3217_; 
v_res_3216_ = l_Lean_Expr_isLet(v_x_3215_);
lean_dec_ref(v_x_3215_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHave(lean_object* v_x_3218_){
_start:
{
if (lean_obj_tag(v_x_3218_) == 8)
{
uint8_t v_nondep_3219_; 
v_nondep_3219_ = lean_ctor_get_uint8(v_x_3218_, sizeof(void*)*4 + 8);
return v_nondep_3219_;
}
else
{
uint8_t v___x_3220_; 
v___x_3220_ = 0;
return v___x_3220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHave___boxed(lean_object* v_x_3221_){
_start:
{
uint8_t v_res_3222_; lean_object* v_r_3223_; 
v_res_3222_ = l_Lean_Expr_isHave(v_x_3221_);
lean_dec_ref(v_x_3221_);
v_r_3223_ = lean_box(v_res_3222_);
return v_r_3223_;
}
}
LEAN_EXPORT uint8_t lean_expr_is_have(lean_object* v_a_3224_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = l_Lean_Expr_isHave(v_a_3224_);
lean_dec_ref(v_a_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHaveEx___boxed(lean_object* v_a_3226_){
_start:
{
uint8_t v_res_3227_; lean_object* v_r_3228_; 
v_res_3227_ = lean_expr_is_have(v_a_3226_);
v_r_3228_ = lean_box(v_res_3227_);
return v_r_3228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 10)
{
uint8_t v___x_3230_; 
v___x_3230_ = 1;
return v___x_3230_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = 0;
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* v_x_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Lean_Expr_isMData(v_x_3232_);
lean_dec_ref(v_x_3232_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* v_x_3235_){
_start:
{
if (lean_obj_tag(v_x_3235_) == 9)
{
uint8_t v___x_3236_; 
v___x_3236_ = 1;
return v___x_3236_;
}
else
{
uint8_t v___x_3237_; 
v___x_3237_ = 0;
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* v_x_3238_){
_start:
{
uint8_t v_res_3239_; lean_object* v_r_3240_; 
v_res_3239_ = l_Lean_Expr_isLit(v_x_3238_);
lean_dec_ref(v_x_3238_);
v_r_3240_ = lean_box(v_res_3239_);
return v_r_3240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_appFn_x21_spec__0(lean_object* v_msg_3241_){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = l_Lean_instInhabitedExpr;
v___x_3243_ = lean_panic_fn_borrowed(v___x_3242_, v_msg_3241_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3247_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3248_ = lean_unsigned_to_nat(15u);
v___x_3249_ = lean_unsigned_to_nat(967u);
v___x_3250_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__1));
v___x_3251_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3252_ = l_mkPanicMessageWithDecl(v___x_3251_, v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 5)
{
lean_object* v_fn_3254_; 
v_fn_3254_ = lean_ctor_get(v_x_3253_, 0);
lean_inc_ref(v_fn_3254_);
return v_fn_3254_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_obj_once(&l_Lean_Expr_appFn_x21___closed__3, &l_Lean_Expr_appFn_x21___closed__3_once, _init_l_Lean_Expr_appFn_x21___closed__3);
v___x_3256_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3255_);
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* v_x_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Expr_appFn_x21(v_x_3257_);
lean_dec_ref(v_x_3257_);
return v_res_3258_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3260_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3261_ = lean_unsigned_to_nat(15u);
v___x_3262_ = lean_unsigned_to_nat(971u);
v___x_3263_ = ((lean_object*)(l_Lean_Expr_appArg_x21___closed__0));
v___x_3264_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3265_ = l_mkPanicMessageWithDecl(v___x_3264_, v___x_3263_, v___x_3262_, v___x_3261_, v___x_3260_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* v_x_3266_){
_start:
{
if (lean_obj_tag(v_x_3266_) == 5)
{
lean_object* v_arg_3267_; 
v_arg_3267_ = lean_ctor_get(v_x_3266_, 1);
lean_inc_ref(v_arg_3267_);
return v_arg_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_obj_once(&l_Lean_Expr_appArg_x21___closed__1, &l_Lean_Expr_appArg_x21___closed__1_once, _init_l_Lean_Expr_appArg_x21___closed__1);
v___x_3269_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3268_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* v_x_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Expr_appArg_x21(v_x_3270_);
lean_dec_ref(v_x_3270_);
return v_res_3271_;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3273_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3274_ = lean_unsigned_to_nat(17u);
v___x_3275_ = lean_unsigned_to_nat(976u);
v___x_3276_ = ((lean_object*)(l_Lean_Expr_appFn_x21_x27___closed__0));
v___x_3277_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3278_ = l_mkPanicMessageWithDecl(v___x_3277_, v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* v_x_3279_){
_start:
{
switch(lean_obj_tag(v_x_3279_))
{
case 10:
{
lean_object* v_expr_3280_; 
v_expr_3280_ = lean_ctor_get(v_x_3279_, 1);
v_x_3279_ = v_expr_3280_;
goto _start;
}
case 5:
{
lean_object* v_fn_3282_; 
v_fn_3282_ = lean_ctor_get(v_x_3279_, 0);
lean_inc_ref(v_fn_3282_);
return v_fn_3282_;
}
default: 
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l_Lean_Expr_appFn_x21_x27___closed__1, &l_Lean_Expr_appFn_x21_x27___closed__1_once, _init_l_Lean_Expr_appFn_x21_x27___closed__1);
v___x_3284_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3283_);
return v___x_3284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* v_x_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Expr_appFn_x21_x27(v_x_3285_);
lean_dec_ref(v_x_3285_);
return v_res_3286_;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3288_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_3289_ = lean_unsigned_to_nat(17u);
v___x_3290_ = lean_unsigned_to_nat(981u);
v___x_3291_ = ((lean_object*)(l_Lean_Expr_appArg_x21_x27___closed__0));
v___x_3292_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3293_ = l_mkPanicMessageWithDecl(v___x_3292_, v___x_3291_, v___x_3290_, v___x_3289_, v___x_3288_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* v_x_3294_){
_start:
{
switch(lean_obj_tag(v_x_3294_))
{
case 10:
{
lean_object* v_expr_3295_; 
v_expr_3295_ = lean_ctor_get(v_x_3294_, 1);
v_x_3294_ = v_expr_3295_;
goto _start;
}
case 5:
{
lean_object* v_arg_3297_; 
v_arg_3297_ = lean_ctor_get(v_x_3294_, 1);
lean_inc_ref(v_arg_3297_);
return v_arg_3297_;
}
default: 
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_obj_once(&l_Lean_Expr_appArg_x21_x27___closed__1, &l_Lean_Expr_appArg_x21_x27___closed__1_once, _init_l_Lean_Expr_appArg_x21_x27___closed__1);
v___x_3299_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3298_);
return v___x_3299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* v_x_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Expr_appArg_x21_x27(v_x_3300_);
lean_dec_ref(v_x_3300_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg(lean_object* v_e_3302_){
_start:
{
lean_object* v_arg_3303_; 
v_arg_3303_ = lean_ctor_get(v_e_3302_, 1);
lean_inc_ref(v_arg_3303_);
return v_arg_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___redArg___boxed(lean_object* v_e_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Expr_appArg___redArg(v_e_3304_);
lean_dec_ref(v_e_3304_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg(lean_object* v_e_3306_, lean_object* v_h_3307_){
_start:
{
lean_object* v_arg_3308_; 
v_arg_3308_ = lean_ctor_get(v_e_3306_, 1);
lean_inc_ref(v_arg_3308_);
return v_arg_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg___boxed(lean_object* v_e_3309_, lean_object* v_h_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_Expr_appArg(v_e_3309_, v_h_3310_);
lean_dec_ref(v_e_3309_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg(lean_object* v_e_3312_){
_start:
{
lean_object* v_fn_3313_; 
v_fn_3313_ = lean_ctor_get(v_e_3312_, 0);
lean_inc_ref(v_fn_3313_);
return v_fn_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___redArg___boxed(lean_object* v_e_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Expr_appFn___redArg(v_e_3314_);
lean_dec_ref(v_e_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn(lean_object* v_e_3316_, lean_object* v_h_3317_){
_start:
{
lean_object* v_fn_3318_; 
v_fn_3318_ = lean_ctor_get(v_e_3316_, 0);
lean_inc_ref(v_fn_3318_);
return v_fn_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn___boxed(lean_object* v_e_3319_, lean_object* v_h_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Expr_appFn(v_e_3319_, v_h_3320_);
lean_dec_ref(v_e_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(lean_object* v_msg_3322_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_panic_fn_borrowed(v___x_3323_, v_msg_3322_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3327_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__1));
v___x_3328_ = lean_unsigned_to_nat(14u);
v___x_3329_ = lean_unsigned_to_nat(993u);
v___x_3330_ = ((lean_object*)(l_Lean_Expr_sortLevel_x21___closed__0));
v___x_3331_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3332_ = l_mkPanicMessageWithDecl(v___x_3331_, v___x_3330_, v___x_3329_, v___x_3328_, v___x_3327_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* v_x_3333_){
_start:
{
if (lean_obj_tag(v_x_3333_) == 3)
{
lean_object* v_u_3334_; 
v_u_3334_ = lean_ctor_get(v_x_3333_, 0);
lean_inc(v_u_3334_);
return v_u_3334_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_obj_once(&l_Lean_Expr_sortLevel_x21___closed__2, &l_Lean_Expr_sortLevel_x21___closed__2_once, _init_l_Lean_Expr_sortLevel_x21___closed__2);
v___x_3336_ = l_panic___at___00Lean_Expr_sortLevel_x21_spec__0(v___x_3335_);
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* v_x_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Expr_sortLevel_x21(v_x_3337_);
lean_dec_ref(v_x_3337_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_litValue_x21_spec__0(lean_object* v_msg_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_instInhabitedLiteral_default));
v___x_3341_ = lean_panic_fn_borrowed(v___x_3340_, v_msg_3339_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3344_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__1));
v___x_3345_ = lean_unsigned_to_nat(13u);
v___x_3346_ = lean_unsigned_to_nat(997u);
v___x_3347_ = ((lean_object*)(l_Lean_Expr_litValue_x21___closed__0));
v___x_3348_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3349_ = l_mkPanicMessageWithDecl(v___x_3348_, v___x_3347_, v___x_3346_, v___x_3345_, v___x_3344_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* v_x_3350_){
_start:
{
if (lean_obj_tag(v_x_3350_) == 9)
{
lean_object* v_a_3351_; 
v_a_3351_ = lean_ctor_get(v_x_3350_, 0);
lean_inc_ref(v_a_3351_);
return v_a_3351_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_obj_once(&l_Lean_Expr_litValue_x21___closed__2, &l_Lean_Expr_litValue_x21___closed__2_once, _init_l_Lean_Expr_litValue_x21___closed__2);
v___x_3353_ = l_panic___at___00Lean_Expr_litValue_x21_spec__0(v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21___boxed(lean_object* v_x_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_Expr_litValue_x21(v_x_3354_);
lean_dec_ref(v_x_3354_);
return v_res_3355_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isRawNatLit(lean_object* v_x_3356_){
_start:
{
if (lean_obj_tag(v_x_3356_) == 9)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v_x_3356_, 0);
if (lean_obj_tag(v_a_3357_) == 0)
{
uint8_t v___x_3358_; 
v___x_3358_ = 1;
return v___x_3358_;
}
else
{
uint8_t v___x_3359_; 
v___x_3359_ = 0;
return v___x_3359_;
}
}
else
{
uint8_t v___x_3360_; 
v___x_3360_ = 0;
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isRawNatLit___boxed(lean_object* v_x_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_Expr_isRawNatLit(v_x_3361_);
lean_dec_ref(v_x_3361_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object* v_x_3364_){
_start:
{
if (lean_obj_tag(v_x_3364_) == 9)
{
lean_object* v_a_3365_; 
v_a_3365_ = lean_ctor_get(v_x_3364_, 0);
lean_inc_ref(v_a_3365_);
lean_dec_ref_known(v_x_3364_, 1);
if (lean_obj_tag(v_a_3365_) == 0)
{
lean_object* v_val_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_val_3366_ = lean_ctor_get(v_a_3365_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_a_3365_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v_a_3365_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_val_3366_);
lean_dec(v_a_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 1);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_val_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v___x_3374_; 
lean_dec_ref(v_a_3365_);
v___x_3374_ = lean_box(0);
return v___x_3374_;
}
}
else
{
lean_object* v___x_3375_; 
lean_dec_ref(v_x_3364_);
v___x_3375_ = lean_box(0);
return v___x_3375_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 9)
{
lean_object* v_a_3377_; 
v_a_3377_ = lean_ctor_get(v_x_3376_, 0);
if (lean_obj_tag(v_a_3377_) == 1)
{
uint8_t v___x_3378_; 
v___x_3378_ = 1;
return v___x_3378_;
}
else
{
uint8_t v___x_3379_; 
v___x_3379_ = 0;
return v___x_3379_;
}
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = 0;
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* v_x_3381_){
_start:
{
uint8_t v_res_3382_; lean_object* v_r_3383_; 
v_res_3382_ = l_Lean_Expr_isStringLit(v_x_3381_);
lean_dec_ref(v_x_3381_);
v_r_3383_ = lean_box(v_res_3382_);
return v_r_3383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* v_x_3388_){
_start:
{
if (lean_obj_tag(v_x_3388_) == 5)
{
lean_object* v_fn_3389_; 
v_fn_3389_ = lean_ctor_get(v_x_3388_, 0);
if (lean_obj_tag(v_fn_3389_) == 4)
{
lean_object* v_arg_3390_; lean_object* v_declName_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v_arg_3390_ = lean_ctor_get(v_x_3388_, 1);
v_declName_3391_ = lean_ctor_get(v_fn_3389_, 0);
v___x_3392_ = ((lean_object*)(l_Lean_Expr_isCharLit___closed__1));
v___x_3393_ = lean_name_eq(v_declName_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
return v___x_3393_;
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = l_Lean_Expr_isRawNatLit(v_arg_3390_);
return v___x_3394_;
}
}
else
{
uint8_t v___x_3395_; 
v___x_3395_ = 0;
return v___x_3395_;
}
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = 0;
return v___x_3396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* v_x_3397_){
_start:
{
uint8_t v_res_3398_; lean_object* v_r_3399_; 
v_res_3398_ = l_Lean_Expr_isCharLit(v_x_3397_);
lean_dec_ref(v_x_3397_);
v_r_3399_ = lean_box(v_res_3398_);
return v_r_3399_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constName_x21_spec__0(lean_object* v_msg_3400_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_box(0);
v___x_3402_ = lean_panic_fn_borrowed(v___x_3401_, v_msg_3400_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3405_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3406_ = lean_unsigned_to_nat(17u);
v___x_3407_ = lean_unsigned_to_nat(1021u);
v___x_3408_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__0));
v___x_3409_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3410_ = l_mkPanicMessageWithDecl(v___x_3409_, v___x_3408_, v___x_3407_, v___x_3406_, v___x_3405_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* v_x_3411_){
_start:
{
if (lean_obj_tag(v_x_3411_) == 4)
{
lean_object* v_declName_3412_; 
v_declName_3412_ = lean_ctor_get(v_x_3411_, 0);
lean_inc(v_declName_3412_);
return v_declName_3412_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_obj_once(&l_Lean_Expr_constName_x21___closed__2, &l_Lean_Expr_constName_x21___closed__2_once, _init_l_Lean_Expr_constName_x21___closed__2);
v___x_3414_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* v_x_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Expr_constName_x21(v_x_3415_);
lean_dec_ref(v_x_3415_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* v_x_3417_){
_start:
{
if (lean_obj_tag(v_x_3417_) == 4)
{
lean_object* v_declName_3418_; lean_object* v___x_3419_; 
v_declName_3418_ = lean_ctor_get(v_x_3417_, 0);
lean_inc(v_declName_3418_);
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_declName_3418_);
return v___x_3419_;
}
else
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_box(0);
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* v_x_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Expr_constName_x3f(v_x_3421_);
lean_dec_ref(v_x_3421_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName(lean_object* v_e_3423_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Expr_constName_x3f(v_e_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
return v___x_3425_;
}
else
{
lean_object* v_val_3426_; 
v_val_3426_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v___x_3424_, 1);
return v_val_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName___boxed(lean_object* v_e_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Expr_constName(v_e_3427_);
lean_dec_ref(v_e_3427_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_constLevels_x21_spec__0(lean_object* v_msg_3429_){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_panic_fn_borrowed(v___x_3430_, v_msg_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3433_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_3434_ = lean_unsigned_to_nat(18u);
v___x_3435_ = lean_unsigned_to_nat(1041u);
v___x_3436_ = ((lean_object*)(l_Lean_Expr_constLevels_x21___closed__0));
v___x_3437_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3438_ = l_mkPanicMessageWithDecl(v___x_3437_, v___x_3436_, v___x_3435_, v___x_3434_, v___x_3433_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* v_x_3439_){
_start:
{
if (lean_obj_tag(v_x_3439_) == 4)
{
lean_object* v_us_3440_; 
v_us_3440_ = lean_ctor_get(v_x_3439_, 1);
lean_inc(v_us_3440_);
return v_us_3440_;
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_obj_once(&l_Lean_Expr_constLevels_x21___closed__1, &l_Lean_Expr_constLevels_x21___closed__1_once, _init_l_Lean_Expr_constLevels_x21___closed__1);
v___x_3442_ = l_panic___at___00Lean_Expr_constLevels_x21_spec__0(v___x_3441_);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* v_x_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Expr_constLevels_x21(v_x_3443_);
lean_dec_ref(v_x_3443_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(lean_object* v_msg_3445_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_panic_fn_borrowed(v___x_3446_, v_msg_3445_);
return v___x_3447_;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3450_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__1));
v___x_3451_ = lean_unsigned_to_nat(16u);
v___x_3452_ = lean_unsigned_to_nat(1045u);
v___x_3453_ = ((lean_object*)(l_Lean_Expr_bvarIdx_x21___closed__0));
v___x_3454_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3455_ = l_mkPanicMessageWithDecl(v___x_3454_, v___x_3453_, v___x_3452_, v___x_3451_, v___x_3450_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* v_x_3456_){
_start:
{
if (lean_obj_tag(v_x_3456_) == 0)
{
lean_object* v_deBruijnIndex_3457_; 
v_deBruijnIndex_3457_ = lean_ctor_get(v_x_3456_, 0);
lean_inc(v_deBruijnIndex_3457_);
return v_deBruijnIndex_3457_;
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_obj_once(&l_Lean_Expr_bvarIdx_x21___closed__2, &l_Lean_Expr_bvarIdx_x21___closed__2_once, _init_l_Lean_Expr_bvarIdx_x21___closed__2);
v___x_3459_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3458_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* v_x_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Expr_bvarIdx_x21(v_x_3460_);
lean_dec_ref(v_x_3460_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_fvarId_x21_spec__0(lean_object* v_msg_3462_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_panic_fn_borrowed(v___x_3463_, v_msg_3462_);
return v___x_3464_;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3467_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_3468_ = lean_unsigned_to_nat(14u);
v___x_3469_ = lean_unsigned_to_nat(1049u);
v___x_3470_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__0));
v___x_3471_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3472_ = l_mkPanicMessageWithDecl(v___x_3471_, v___x_3470_, v___x_3469_, v___x_3468_, v___x_3467_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* v_x_3473_){
_start:
{
if (lean_obj_tag(v_x_3473_) == 1)
{
lean_object* v_fvarId_3474_; 
v_fvarId_3474_ = lean_ctor_get(v_x_3473_, 0);
lean_inc(v_fvarId_3474_);
return v_fvarId_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = lean_obj_once(&l_Lean_Expr_fvarId_x21___closed__2, &l_Lean_Expr_fvarId_x21___closed__2_once, _init_l_Lean_Expr_fvarId_x21___closed__2);
v___x_3476_ = l_panic___at___00Lean_Expr_fvarId_x21_spec__0(v___x_3475_);
return v___x_3476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* v_x_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Expr_fvarId_x21(v_x_3477_);
lean_dec_ref(v_x_3477_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f(lean_object* v_x_3479_){
_start:
{
if (lean_obj_tag(v_x_3479_) == 1)
{
lean_object* v_fvarId_3480_; lean_object* v___x_3481_; 
v_fvarId_3480_ = lean_ctor_get(v_x_3479_, 0);
lean_inc(v_fvarId_3480_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_fvarId_3480_);
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_box(0);
return v___x_3482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x3f___boxed(lean_object* v_x_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Expr_fvarId_x3f(v_x_3483_);
lean_dec_ref(v_x_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_mvarId_x21_spec__0(lean_object* v_msg_3485_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_panic_fn_borrowed(v___x_3486_, v_msg_3485_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3490_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__1));
v___x_3491_ = lean_unsigned_to_nat(14u);
v___x_3492_ = lean_unsigned_to_nat(1057u);
v___x_3493_ = ((lean_object*)(l_Lean_Expr_mvarId_x21___closed__0));
v___x_3494_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3495_ = l_mkPanicMessageWithDecl(v___x_3494_, v___x_3493_, v___x_3492_, v___x_3491_, v___x_3490_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* v_x_3496_){
_start:
{
if (lean_obj_tag(v_x_3496_) == 2)
{
lean_object* v_mvarId_3497_; 
v_mvarId_3497_ = lean_ctor_get(v_x_3496_, 0);
lean_inc(v_mvarId_3497_);
return v_mvarId_3497_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_obj_once(&l_Lean_Expr_mvarId_x21___closed__2, &l_Lean_Expr_mvarId_x21___closed__2_once, _init_l_Lean_Expr_mvarId_x21___closed__2);
v___x_3499_ = l_panic___at___00Lean_Expr_mvarId_x21_spec__0(v___x_3498_);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* v_x_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Lean_Expr_mvarId_x21(v_x_3500_);
lean_dec_ref(v_x_3500_);
return v_res_3501_;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3504_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3505_ = lean_unsigned_to_nat(23u);
v___x_3506_ = lean_unsigned_to_nat(1062u);
v___x_3507_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__0));
v___x_3508_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3509_ = l_mkPanicMessageWithDecl(v___x_3508_, v___x_3507_, v___x_3506_, v___x_3505_, v___x_3504_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* v_x_3510_){
_start:
{
switch(lean_obj_tag(v_x_3510_))
{
case 7:
{
lean_object* v_binderName_3511_; 
v_binderName_3511_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_binderName_3511_);
return v_binderName_3511_;
}
case 6:
{
lean_object* v_binderName_3512_; 
v_binderName_3512_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_binderName_3512_);
return v_binderName_3512_;
}
default: 
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l_Lean_Expr_bindingName_x21___closed__2, &l_Lean_Expr_bindingName_x21___closed__2_once, _init_l_Lean_Expr_bindingName_x21___closed__2);
v___x_3514_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3513_);
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* v_x_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_Expr_bindingName_x21(v_x_3515_);
lean_dec_ref(v_x_3515_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3518_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3519_ = lean_unsigned_to_nat(23u);
v___x_3520_ = lean_unsigned_to_nat(1067u);
v___x_3521_ = ((lean_object*)(l_Lean_Expr_bindingDomain_x21___closed__0));
v___x_3522_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3523_ = l_mkPanicMessageWithDecl(v___x_3522_, v___x_3521_, v___x_3520_, v___x_3519_, v___x_3518_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* v_x_3524_){
_start:
{
switch(lean_obj_tag(v_x_3524_))
{
case 7:
{
lean_object* v_binderType_3525_; 
v_binderType_3525_ = lean_ctor_get(v_x_3524_, 1);
lean_inc_ref(v_binderType_3525_);
return v_binderType_3525_;
}
case 6:
{
lean_object* v_binderType_3526_; 
v_binderType_3526_ = lean_ctor_get(v_x_3524_, 1);
lean_inc_ref(v_binderType_3526_);
return v_binderType_3526_;
}
default: 
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_obj_once(&l_Lean_Expr_bindingDomain_x21___closed__1, &l_Lean_Expr_bindingDomain_x21___closed__1_once, _init_l_Lean_Expr_bindingDomain_x21___closed__1);
v___x_3528_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3527_);
return v___x_3528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* v_x_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Expr_bindingDomain_x21(v_x_3529_);
lean_dec_ref(v_x_3529_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3532_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3533_ = lean_unsigned_to_nat(23u);
v___x_3534_ = lean_unsigned_to_nat(1072u);
v___x_3535_ = ((lean_object*)(l_Lean_Expr_bindingBody_x21___closed__0));
v___x_3536_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3537_ = l_mkPanicMessageWithDecl(v___x_3536_, v___x_3535_, v___x_3534_, v___x_3533_, v___x_3532_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* v_x_3538_){
_start:
{
switch(lean_obj_tag(v_x_3538_))
{
case 7:
{
lean_object* v_body_3539_; 
v_body_3539_ = lean_ctor_get(v_x_3538_, 2);
lean_inc_ref(v_body_3539_);
return v_body_3539_;
}
case 6:
{
lean_object* v_body_3540_; 
v_body_3540_ = lean_ctor_get(v_x_3538_, 2);
lean_inc_ref(v_body_3540_);
return v_body_3540_;
}
default: 
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l_Lean_Expr_bindingBody_x21___closed__1, &l_Lean_Expr_bindingBody_x21___closed__1_once, _init_l_Lean_Expr_bindingBody_x21___closed__1);
v___x_3542_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3541_);
return v___x_3542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* v_x_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Expr_bindingBody_x21(v_x_3543_);
lean_dec_ref(v_x_3543_);
return v_res_3544_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(lean_object* v_msg_3545_){
_start:
{
uint8_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3546_ = 0;
v___x_3547_ = lean_box(v___x_3546_);
v___x_3548_ = lean_panic_fn_borrowed(v___x_3547_, v_msg_3545_);
lean_dec(v___x_3547_);
v___x_3549_ = lean_unbox(v___x_3548_);
lean_dec(v___x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0___boxed(lean_object* v_msg_3550_){
_start:
{
uint8_t v_res_3551_; lean_object* v_r_3552_; 
v_res_3551_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v_msg_3550_);
v_r_3552_ = lean_box(v_res_3551_);
return v_r_3552_;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3554_ = ((lean_object*)(l_Lean_Expr_bindingName_x21___closed__1));
v___x_3555_ = lean_unsigned_to_nat(24u);
v___x_3556_ = lean_unsigned_to_nat(1077u);
v___x_3557_ = ((lean_object*)(l_Lean_Expr_bindingInfo_x21___closed__0));
v___x_3558_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3559_ = l_mkPanicMessageWithDecl(v___x_3558_, v___x_3557_, v___x_3556_, v___x_3555_, v___x_3554_);
return v___x_3559_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* v_x_3560_){
_start:
{
switch(lean_obj_tag(v_x_3560_))
{
case 7:
{
uint8_t v_binderInfo_3561_; 
v_binderInfo_3561_ = lean_ctor_get_uint8(v_x_3560_, sizeof(void*)*3 + 8);
return v_binderInfo_3561_;
}
case 6:
{
uint8_t v_binderInfo_3562_; 
v_binderInfo_3562_ = lean_ctor_get_uint8(v_x_3560_, sizeof(void*)*3 + 8);
return v_binderInfo_3562_;
}
default: 
{
lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3563_ = lean_obj_once(&l_Lean_Expr_bindingInfo_x21___closed__1, &l_Lean_Expr_bindingInfo_x21___closed__1_once, _init_l_Lean_Expr_bindingInfo_x21___closed__1);
v___x_3564_ = l_panic___at___00Lean_Expr_bindingInfo_x21_spec__0(v___x_3563_);
return v___x_3564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* v_x_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_Lean_Expr_bindingInfo_x21(v_x_3565_);
lean_dec_ref(v_x_3565_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg(lean_object* v_x_3568_){
_start:
{
lean_object* v_binderName_3569_; 
v_binderName_3569_ = lean_ctor_get(v_x_3568_, 0);
lean_inc(v_binderName_3569_);
return v_binderName_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___redArg___boxed(lean_object* v_x_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Expr_forallName___redArg(v_x_3570_);
lean_dec_ref(v_x_3570_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName(lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
lean_object* v_binderName_3574_; 
v_binderName_3574_ = lean_ctor_get(v_x_3572_, 0);
lean_inc(v_binderName_3574_);
return v_binderName_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallName___boxed(lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Expr_forallName(v_x_3575_, v_x_3576_);
lean_dec_ref(v_x_3575_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg(lean_object* v_x_3578_){
_start:
{
lean_object* v_binderType_3579_; 
v_binderType_3579_ = lean_ctor_get(v_x_3578_, 1);
lean_inc_ref(v_binderType_3579_);
return v_binderType_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___redArg___boxed(lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Expr_forallDomain___redArg(v_x_3580_);
lean_dec_ref(v_x_3580_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain(lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v_binderType_3584_; 
v_binderType_3584_ = lean_ctor_get(v_x_3582_, 1);
lean_inc_ref(v_binderType_3584_);
return v_binderType_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallDomain___boxed(lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Expr_forallDomain(v_x_3585_, v_x_3586_);
lean_dec_ref(v_x_3585_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg(lean_object* v_x_3588_){
_start:
{
lean_object* v_body_3589_; 
v_body_3589_ = lean_ctor_get(v_x_3588_, 2);
lean_inc_ref(v_body_3589_);
return v_body_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___redArg___boxed(lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_Expr_forallBody___redArg(v_x_3590_);
lean_dec_ref(v_x_3590_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody(lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_body_3594_; 
v_body_3594_ = lean_ctor_get(v_x_3592_, 2);
lean_inc_ref(v_body_3594_);
return v_body_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallBody___boxed(lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Expr_forallBody(v_x_3595_, v_x_3596_);
lean_dec_ref(v_x_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo___redArg(lean_object* v_x_3598_){
_start:
{
uint8_t v_binderInfo_3599_; 
v_binderInfo_3599_ = lean_ctor_get_uint8(v_x_3598_, sizeof(void*)*3 + 8);
return v_binderInfo_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___redArg___boxed(lean_object* v_x_3600_){
_start:
{
uint8_t v_res_3601_; lean_object* v_r_3602_; 
v_res_3601_ = l_Lean_Expr_forallInfo___redArg(v_x_3600_);
lean_dec_ref(v_x_3600_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_forallInfo(lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
uint8_t v_binderInfo_3605_; 
v_binderInfo_3605_ = lean_ctor_get_uint8(v_x_3603_, sizeof(void*)*3 + 8);
return v_binderInfo_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallInfo___boxed(lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
uint8_t v_res_3608_; lean_object* v_r_3609_; 
v_res_3608_ = l_Lean_Expr_forallInfo(v_x_3606_, v_x_3607_);
lean_dec_ref(v_x_3606_);
v_r_3609_ = lean_box(v_res_3608_);
return v_r_3609_;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3612_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3613_ = lean_unsigned_to_nat(17u);
v___x_3614_ = lean_unsigned_to_nat(1093u);
v___x_3615_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__0));
v___x_3616_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3617_ = l_mkPanicMessageWithDecl(v___x_3616_, v___x_3615_, v___x_3614_, v___x_3613_, v___x_3612_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* v_x_3618_){
_start:
{
if (lean_obj_tag(v_x_3618_) == 8)
{
lean_object* v_declName_3619_; 
v_declName_3619_ = lean_ctor_get(v_x_3618_, 0);
lean_inc(v_declName_3619_);
return v_declName_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_obj_once(&l_Lean_Expr_letName_x21___closed__2, &l_Lean_Expr_letName_x21___closed__2_once, _init_l_Lean_Expr_letName_x21___closed__2);
v___x_3621_ = l_panic___at___00Lean_Expr_constName_x21_spec__0(v___x_3620_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* v_x_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Expr_letName_x21(v_x_3622_);
lean_dec_ref(v_x_3622_);
return v_res_3623_;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3625_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3626_ = lean_unsigned_to_nat(19u);
v___x_3627_ = lean_unsigned_to_nat(1097u);
v___x_3628_ = ((lean_object*)(l_Lean_Expr_letType_x21___closed__0));
v___x_3629_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3630_ = l_mkPanicMessageWithDecl(v___x_3629_, v___x_3628_, v___x_3627_, v___x_3626_, v___x_3625_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* v_x_3631_){
_start:
{
if (lean_obj_tag(v_x_3631_) == 8)
{
lean_object* v_type_3632_; 
v_type_3632_ = lean_ctor_get(v_x_3631_, 1);
lean_inc_ref(v_type_3632_);
return v_type_3632_;
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_obj_once(&l_Lean_Expr_letType_x21___closed__1, &l_Lean_Expr_letType_x21___closed__1_once, _init_l_Lean_Expr_letType_x21___closed__1);
v___x_3634_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3633_);
return v___x_3634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* v_x_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_Expr_letType_x21(v_x_3635_);
lean_dec_ref(v_x_3635_);
return v_res_3636_;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3638_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3639_ = lean_unsigned_to_nat(21u);
v___x_3640_ = lean_unsigned_to_nat(1101u);
v___x_3641_ = ((lean_object*)(l_Lean_Expr_letValue_x21___closed__0));
v___x_3642_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3643_ = l_mkPanicMessageWithDecl(v___x_3642_, v___x_3641_, v___x_3640_, v___x_3639_, v___x_3638_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* v_x_3644_){
_start:
{
if (lean_obj_tag(v_x_3644_) == 8)
{
lean_object* v_value_3645_; 
v_value_3645_ = lean_ctor_get(v_x_3644_, 2);
lean_inc_ref(v_value_3645_);
return v_value_3645_;
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_obj_once(&l_Lean_Expr_letValue_x21___closed__1, &l_Lean_Expr_letValue_x21___closed__1_once, _init_l_Lean_Expr_letValue_x21___closed__1);
v___x_3647_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3646_);
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* v_x_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Expr_letValue_x21(v_x_3648_);
lean_dec_ref(v_x_3648_);
return v_res_3649_;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3651_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3652_ = lean_unsigned_to_nat(23u);
v___x_3653_ = lean_unsigned_to_nat(1105u);
v___x_3654_ = ((lean_object*)(l_Lean_Expr_letBody_x21___closed__0));
v___x_3655_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3656_ = l_mkPanicMessageWithDecl(v___x_3655_, v___x_3654_, v___x_3653_, v___x_3652_, v___x_3651_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* v_x_3657_){
_start:
{
if (lean_obj_tag(v_x_3657_) == 8)
{
lean_object* v_body_3658_; 
v_body_3658_ = lean_ctor_get(v_x_3657_, 3);
lean_inc_ref(v_body_3658_);
return v_body_3658_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_obj_once(&l_Lean_Expr_letBody_x21___closed__1, &l_Lean_Expr_letBody_x21___closed__1_once, _init_l_Lean_Expr_letBody_x21___closed__1);
v___x_3660_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3659_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* v_x_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_Expr_letBody_x21(v_x_3661_);
lean_dec_ref(v_x_3661_);
return v_res_3662_;
}
}
LEAN_EXPORT uint8_t l_panic___at___00Lean_Expr_letNondep_x21_spec__0(lean_object* v_msg_3663_){
_start:
{
uint8_t v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3664_ = 0;
v___x_3665_ = lean_box(v___x_3664_);
v___x_3666_ = lean_panic_fn_borrowed(v___x_3665_, v_msg_3663_);
lean_dec(v___x_3665_);
v___x_3667_ = lean_unbox(v___x_3666_);
lean_dec(v___x_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_letNondep_x21_spec__0___boxed(lean_object* v_msg_3668_){
_start:
{
uint8_t v_res_3669_; lean_object* v_r_3670_; 
v_res_3669_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v_msg_3668_);
v_r_3670_ = lean_box(v_res_3669_);
return v_r_3670_;
}
}
static lean_object* _init_l_Lean_Expr_letNondep_x21___closed__1(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3672_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_3673_ = lean_unsigned_to_nat(27u);
v___x_3674_ = lean_unsigned_to_nat(1109u);
v___x_3675_ = ((lean_object*)(l_Lean_Expr_letNondep_x21___closed__0));
v___x_3676_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3677_ = l_mkPanicMessageWithDecl(v___x_3676_, v___x_3675_, v___x_3674_, v___x_3673_, v___x_3672_);
return v___x_3677_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_letNondep_x21(lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 8)
{
uint8_t v_nondep_3679_; 
v_nondep_3679_ = lean_ctor_get_uint8(v_x_3678_, sizeof(void*)*4 + 8);
return v_nondep_3679_;
}
else
{
lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = lean_obj_once(&l_Lean_Expr_letNondep_x21___closed__1, &l_Lean_Expr_letNondep_x21___closed__1_once, _init_l_Lean_Expr_letNondep_x21___closed__1);
v___x_3681_ = l_panic___at___00Lean_Expr_letNondep_x21_spec__0(v___x_3680_);
return v___x_3681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letNondep_x21___boxed(lean_object* v_x_3682_){
_start:
{
uint8_t v_res_3683_; lean_object* v_r_3684_; 
v_res_3683_ = l_Lean_Expr_letNondep_x21(v_x_3682_);
lean_dec_ref(v_x_3682_);
v_r_3684_ = lean_box(v_res_3683_);
return v_r_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* v_x_3685_){
_start:
{
if (lean_obj_tag(v_x_3685_) == 10)
{
lean_object* v_expr_3686_; 
v_expr_3686_ = lean_ctor_get(v_x_3685_, 1);
v_x_3685_ = v_expr_3686_;
goto _start;
}
else
{
lean_inc_ref(v_x_3685_);
return v_x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* v_x_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Expr_consumeMData(v_x_3688_);
lean_dec_ref(v_x_3688_);
return v_res_3689_;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3692_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__1));
v___x_3693_ = lean_unsigned_to_nat(17u);
v___x_3694_ = lean_unsigned_to_nat(1117u);
v___x_3695_ = ((lean_object*)(l_Lean_Expr_mdataExpr_x21___closed__0));
v___x_3696_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3697_ = l_mkPanicMessageWithDecl(v___x_3696_, v___x_3695_, v___x_3694_, v___x_3693_, v___x_3692_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* v_x_3698_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 10)
{
lean_object* v_expr_3699_; 
v_expr_3699_ = lean_ctor_get(v_x_3698_, 1);
lean_inc_ref(v_expr_3699_);
return v_expr_3699_;
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_obj_once(&l_Lean_Expr_mdataExpr_x21___closed__2, &l_Lean_Expr_mdataExpr_x21___closed__2_once, _init_l_Lean_Expr_mdataExpr_x21___closed__2);
v___x_3701_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3700_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* v_x_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Expr_mdataExpr_x21(v_x_3702_);
lean_dec_ref(v_x_3702_);
return v_res_3703_;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3706_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3707_ = lean_unsigned_to_nat(18u);
v___x_3708_ = lean_unsigned_to_nat(1121u);
v___x_3709_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__0));
v___x_3710_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3711_ = l_mkPanicMessageWithDecl(v___x_3710_, v___x_3709_, v___x_3708_, v___x_3707_, v___x_3706_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* v_x_3712_){
_start:
{
if (lean_obj_tag(v_x_3712_) == 11)
{
lean_object* v_struct_3713_; 
v_struct_3713_ = lean_ctor_get(v_x_3712_, 2);
lean_inc_ref(v_struct_3713_);
return v_struct_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_obj_once(&l_Lean_Expr_projExpr_x21___closed__2, &l_Lean_Expr_projExpr_x21___closed__2_once, _init_l_Lean_Expr_projExpr_x21___closed__2);
v___x_3715_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_3714_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Expr_projExpr_x21(v_x_3716_);
lean_dec_ref(v_x_3716_);
return v_res_3717_;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3719_ = ((lean_object*)(l_Lean_Expr_projExpr_x21___closed__1));
v___x_3720_ = lean_unsigned_to_nat(18u);
v___x_3721_ = lean_unsigned_to_nat(1125u);
v___x_3722_ = ((lean_object*)(l_Lean_Expr_projIdx_x21___closed__0));
v___x_3723_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3724_ = l_mkPanicMessageWithDecl(v___x_3723_, v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* v_x_3725_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 11)
{
lean_object* v_idx_3726_; 
v_idx_3726_ = lean_ctor_get(v_x_3725_, 1);
lean_inc(v_idx_3726_);
return v_idx_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = lean_obj_once(&l_Lean_Expr_projIdx_x21___closed__1, &l_Lean_Expr_projIdx_x21___closed__1_once, _init_l_Lean_Expr_projIdx_x21___closed__1);
v___x_3728_ = l_panic___at___00Lean_Expr_bvarIdx_x21_spec__0(v___x_3727_);
return v___x_3728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* v_x_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Expr_projIdx_x21(v_x_3729_);
lean_dec_ref(v_x_3729_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* v_x_3731_){
_start:
{
if (lean_obj_tag(v_x_3731_) == 7)
{
lean_object* v_body_3732_; 
v_body_3732_ = lean_ctor_get(v_x_3731_, 2);
v_x_3731_ = v_body_3732_;
goto _start;
}
else
{
lean_inc_ref(v_x_3731_);
return v_x_3731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Expr_getForallBody(v_x_3734_);
lean_dec_ref(v_x_3734_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth(lean_object* v_x_3736_, lean_object* v_x_3737_){
_start:
{
lean_object* v_zero_3738_; uint8_t v_isZero_3739_; 
v_zero_3738_ = lean_unsigned_to_nat(0u);
v_isZero_3739_ = lean_nat_dec_eq(v_x_3736_, v_zero_3738_);
if (v_isZero_3739_ == 1)
{
lean_dec(v_x_3736_);
lean_inc_ref(v_x_3737_);
return v_x_3737_;
}
else
{
if (lean_obj_tag(v_x_3737_) == 7)
{
lean_object* v_body_3740_; lean_object* v_one_3741_; lean_object* v_n_3742_; 
v_body_3740_ = lean_ctor_get(v_x_3737_, 2);
v_one_3741_ = lean_unsigned_to_nat(1u);
v_n_3742_ = lean_nat_sub(v_x_3736_, v_one_3741_);
lean_dec(v_x_3736_);
v_x_3736_ = v_n_3742_;
v_x_3737_ = v_body_3740_;
goto _start;
}
else
{
lean_dec(v_x_3736_);
lean_inc_ref(v_x_3737_);
return v_x_3737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBodyMaxDepth___boxed(lean_object* v_x_3744_, lean_object* v_x_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Expr_getForallBodyMaxDepth(v_x_3744_, v_x_3745_);
lean_dec_ref(v_x_3745_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames(lean_object* v_x_3747_){
_start:
{
if (lean_obj_tag(v_x_3747_) == 7)
{
lean_object* v_binderName_3748_; lean_object* v_body_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_binderName_3748_ = lean_ctor_get(v_x_3747_, 0);
v_body_3749_ = lean_ctor_get(v_x_3747_, 2);
v___x_3750_ = l_Lean_Expr_getForallBinderNames(v_body_3749_);
lean_inc(v_binderName_3748_);
v___x_3751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_binderName_3748_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_box(0);
return v___x_3752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBinderNames___boxed(lean_object* v_x_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Expr_getForallBinderNames(v_x_3753_);
lean_dec_ref(v_x_3753_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls(lean_object* v_x_3755_){
_start:
{
switch(lean_obj_tag(v_x_3755_))
{
case 10:
{
lean_object* v_expr_3756_; 
v_expr_3756_ = lean_ctor_get(v_x_3755_, 1);
v_x_3755_ = v_expr_3756_;
goto _start;
}
case 7:
{
lean_object* v_body_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v_body_3758_ = lean_ctor_get(v_x_3755_, 2);
v___x_3759_ = l_Lean_Expr_getNumHeadForalls(v_body_3758_);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_nat_add(v___x_3759_, v___x_3760_);
lean_dec(v___x_3759_);
return v___x_3761_;
}
default: 
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_unsigned_to_nat(0u);
return v___x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadForalls___boxed(lean_object* v_x_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Expr_getNumHeadForalls(v_x_3763_);
lean_dec_ref(v_x_3763_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 5)
{
lean_object* v_fn_3766_; 
v_fn_3766_ = lean_ctor_get(v_x_3765_, 0);
v_x_3765_ = v_fn_3766_;
goto _start;
}
else
{
lean_inc_ref(v_x_3765_);
return v_x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* v_x_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Expr_getAppFn(v_x_3768_);
lean_dec_ref(v_x_3768_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27(lean_object* v_x_3770_){
_start:
{
switch(lean_obj_tag(v_x_3770_))
{
case 5:
{
lean_object* v_fn_3771_; 
v_fn_3771_ = lean_ctor_get(v_x_3770_, 0);
v_x_3770_ = v_fn_3771_;
goto _start;
}
case 10:
{
lean_object* v_expr_3773_; 
v_expr_3773_ = lean_ctor_get(v_x_3770_, 1);
v_x_3770_ = v_expr_3773_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_3770_);
return v_x_3770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn_x27___boxed(lean_object* v_x_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Expr_getAppFn_x27(v_x_3775_);
lean_dec_ref(v_x_3775_);
return v_res_3776_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* v_e_3777_, lean_object* v_n_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Expr_getAppFn(v_e_3777_);
if (lean_obj_tag(v___x_3779_) == 4)
{
lean_object* v_declName_3780_; uint8_t v___x_3781_; 
v_declName_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_declName_3780_);
lean_dec_ref_known(v___x_3779_, 2);
v___x_3781_ = lean_name_eq(v_declName_3780_, v_n_3778_);
lean_dec(v_declName_3780_);
return v___x_3781_;
}
else
{
uint8_t v___x_3782_; 
lean_dec_ref(v___x_3779_);
v___x_3782_ = 0;
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* v_e_3783_, lean_object* v_n_3784_){
_start:
{
uint8_t v_res_3785_; lean_object* v_r_3786_; 
v_res_3785_ = l_Lean_Expr_isAppOf(v_e_3783_, v_n_3784_);
lean_dec(v_n_3784_);
lean_dec_ref(v_e_3783_);
v_r_3786_ = lean_box(v_res_3785_);
return v_r_3786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* v_x_3787_, lean_object* v_x_3788_, lean_object* v_x_3789_){
_start:
{
switch(lean_obj_tag(v_x_3787_))
{
case 4:
{
lean_object* v_declName_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v_declName_3790_ = lean_ctor_get(v_x_3787_, 0);
v___x_3791_ = lean_unsigned_to_nat(0u);
v___x_3792_ = lean_nat_dec_eq(v_x_3789_, v___x_3791_);
lean_dec(v_x_3789_);
if (v___x_3792_ == 0)
{
return v___x_3792_;
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_name_eq(v_declName_3790_, v_x_3788_);
return v___x_3793_;
}
}
case 5:
{
lean_object* v_fn_3794_; lean_object* v_zero_3795_; uint8_t v_isZero_3796_; 
v_fn_3794_ = lean_ctor_get(v_x_3787_, 0);
v_zero_3795_ = lean_unsigned_to_nat(0u);
v_isZero_3796_ = lean_nat_dec_eq(v_x_3789_, v_zero_3795_);
if (v_isZero_3796_ == 0)
{
lean_object* v_one_3797_; lean_object* v_n_3798_; 
v_one_3797_ = lean_unsigned_to_nat(1u);
v_n_3798_ = lean_nat_sub(v_x_3789_, v_one_3797_);
lean_dec(v_x_3789_);
v_x_3787_ = v_fn_3794_;
v_x_3789_ = v_n_3798_;
goto _start;
}
else
{
uint8_t v___x_3800_; 
lean_dec(v_x_3789_);
v___x_3800_ = 0;
return v___x_3800_;
}
}
default: 
{
uint8_t v___x_3801_; 
lean_dec(v_x_3789_);
v___x_3801_ = 0;
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* v_x_3802_, lean_object* v_x_3803_, lean_object* v_x_3804_){
_start:
{
uint8_t v_res_3805_; lean_object* v_r_3806_; 
v_res_3805_ = l_Lean_Expr_isAppOfArity(v_x_3802_, v_x_3803_, v_x_3804_);
lean_dec(v_x_3803_);
lean_dec_ref(v_x_3802_);
v_r_3806_ = lean_box(v_res_3805_);
return v_r_3806_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* v_x_3807_, lean_object* v_x_3808_, lean_object* v_x_3809_){
_start:
{
switch(lean_obj_tag(v_x_3807_))
{
case 10:
{
lean_object* v_expr_3810_; 
v_expr_3810_ = lean_ctor_get(v_x_3807_, 1);
v_x_3807_ = v_expr_3810_;
goto _start;
}
case 4:
{
lean_object* v_declName_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v_declName_3812_ = lean_ctor_get(v_x_3807_, 0);
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = lean_nat_dec_eq(v_x_3809_, v___x_3813_);
lean_dec(v_x_3809_);
if (v___x_3814_ == 0)
{
return v___x_3814_;
}
else
{
uint8_t v___x_3815_; 
v___x_3815_ = lean_name_eq(v_declName_3812_, v_x_3808_);
return v___x_3815_;
}
}
case 5:
{
lean_object* v_fn_3816_; lean_object* v_zero_3817_; uint8_t v_isZero_3818_; 
v_fn_3816_ = lean_ctor_get(v_x_3807_, 0);
v_zero_3817_ = lean_unsigned_to_nat(0u);
v_isZero_3818_ = lean_nat_dec_eq(v_x_3809_, v_zero_3817_);
if (v_isZero_3818_ == 0)
{
lean_object* v_one_3819_; lean_object* v_n_3820_; 
v_one_3819_ = lean_unsigned_to_nat(1u);
v_n_3820_ = lean_nat_sub(v_x_3809_, v_one_3819_);
lean_dec(v_x_3809_);
v_x_3807_ = v_fn_3816_;
v_x_3809_ = v_n_3820_;
goto _start;
}
else
{
uint8_t v___x_3822_; 
lean_dec(v_x_3809_);
v___x_3822_ = 0;
return v___x_3822_;
}
}
default: 
{
uint8_t v___x_3823_; 
lean_dec(v_x_3809_);
v___x_3823_ = 0;
return v___x_3823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* v_x_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
uint8_t v_res_3827_; lean_object* v_r_3828_; 
v_res_3827_ = l_Lean_Expr_isAppOfArity_x27(v_x_3824_, v_x_3825_, v_x_3826_);
lean_dec(v_x_3825_);
lean_dec_ref(v_x_3824_);
v_r_3828_ = lean_box(v_res_3827_);
return v_r_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* v_x_3829_, lean_object* v_x_3830_){
_start:
{
if (lean_obj_tag(v_x_3829_) == 5)
{
lean_object* v_fn_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v_fn_3831_ = lean_ctor_get(v_x_3829_, 0);
v___x_3832_ = lean_unsigned_to_nat(1u);
v___x_3833_ = lean_nat_add(v_x_3830_, v___x_3832_);
lean_dec(v_x_3830_);
v_x_3829_ = v_fn_3831_;
v_x_3830_ = v___x_3833_;
goto _start;
}
else
{
return v_x_3830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* v_x_3835_, lean_object* v_x_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_x_3835_, v_x_3836_);
lean_dec_ref(v_x_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* v_e_3838_){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_unsigned_to_nat(0u);
v___x_3840_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(v_e_3838_, v___x_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* v_e_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Expr_getAppNumArgs(v_e_3841_);
lean_dec_ref(v_e_3841_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
switch(lean_obj_tag(v_a_3843_))
{
case 10:
{
lean_object* v_expr_3845_; 
v_expr_3845_ = lean_ctor_get(v_a_3843_, 1);
v_a_3843_ = v_expr_3845_;
goto _start;
}
case 5:
{
lean_object* v_fn_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_fn_3847_ = lean_ctor_get(v_a_3843_, 0);
v___x_3848_ = lean_unsigned_to_nat(1u);
v___x_3849_ = lean_nat_add(v_a_3844_, v___x_3848_);
lean_dec(v_a_3844_);
v_a_3843_ = v_fn_3847_;
v_a_3844_ = v___x_3849_;
goto _start;
}
default: 
{
return v_a_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go___boxed(lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_a_3851_, v_a_3852_);
lean_dec_ref(v_a_3851_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object* v_e_3854_){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgs_x27_go(v_e_3854_, v___x_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs_x27___boxed(lean_object* v_e_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Expr_getAppNumArgs_x27(v_e_3857_);
lean_dec_ref(v_e_3857_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn(lean_object* v_x_3859_, lean_object* v_x_3860_){
_start:
{
lean_object* v_zero_3861_; uint8_t v_isZero_3862_; 
v_zero_3861_ = lean_unsigned_to_nat(0u);
v_isZero_3862_ = lean_nat_dec_eq(v_x_3859_, v_zero_3861_);
if (v_isZero_3862_ == 0)
{
if (lean_obj_tag(v_x_3860_) == 5)
{
lean_object* v_fn_3863_; lean_object* v_one_3864_; lean_object* v_n_3865_; 
v_fn_3863_ = lean_ctor_get(v_x_3860_, 0);
v_one_3864_ = lean_unsigned_to_nat(1u);
v_n_3865_ = lean_nat_sub(v_x_3859_, v_one_3864_);
lean_dec(v_x_3859_);
v_x_3859_ = v_n_3865_;
v_x_3860_ = v_fn_3863_;
goto _start;
}
else
{
lean_dec(v_x_3859_);
lean_inc_ref(v_x_3860_);
return v_x_3860_;
}
}
else
{
lean_dec(v_x_3859_);
lean_inc_ref(v_x_3860_);
return v_x_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppFn___boxed(lean_object* v_x_3867_, lean_object* v_x_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_Expr_getBoundedAppFn(v_x_3867_, v_x_3868_);
lean_dec_ref(v_x_3868_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* v_x_3870_, lean_object* v_x_3871_, lean_object* v_x_3872_){
_start:
{
if (lean_obj_tag(v_x_3870_) == 5)
{
lean_object* v_fn_3873_; lean_object* v_arg_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_fn_3873_ = lean_ctor_get(v_x_3870_, 0);
lean_inc_ref(v_fn_3873_);
v_arg_3874_ = lean_ctor_get(v_x_3870_, 1);
lean_inc_ref(v_arg_3874_);
lean_dec_ref_known(v_x_3870_, 2);
v___x_3875_ = lean_array_set(v_x_3871_, v_x_3872_, v_arg_3874_);
v___x_3876_ = lean_unsigned_to_nat(1u);
v___x_3877_ = lean_nat_sub(v_x_3872_, v___x_3876_);
lean_dec(v_x_3872_);
v_x_3870_ = v_fn_3873_;
v_x_3871_ = v___x_3875_;
v_x_3872_ = v___x_3877_;
goto _start;
}
else
{
lean_dec(v_x_3872_);
lean_dec_ref(v_x_3870_);
return v_x_3871_;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__0(void){
_start:
{
lean_object* v___x_3879_; lean_object* v_dummy_3880_; 
v___x_3879_ = lean_box(0);
v_dummy_3880_ = l_Lean_Expr_sort___override(v___x_3879_);
return v_dummy_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* v_e_3881_){
_start:
{
lean_object* v_dummy_3882_; lean_object* v_nargs_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v_dummy_3882_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3883_ = l_Lean_Expr_getAppNumArgs(v_e_3881_);
lean_inc(v_nargs_3883_);
v___x_3884_ = lean_mk_array(v_nargs_3883_, v_dummy_3882_);
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_sub(v_nargs_3883_, v___x_3885_);
lean_dec(v_nargs_3883_);
v___x_3887_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3881_, v___x_3884_, v___x_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 5)
{
lean_object* v_fn_3891_; lean_object* v_arg_3892_; lean_object* v_zero_3893_; uint8_t v_isZero_3894_; 
v_fn_3891_ = lean_ctor_get(v_x_3888_, 0);
lean_inc_ref(v_fn_3891_);
v_arg_3892_ = lean_ctor_get(v_x_3888_, 1);
lean_inc_ref(v_arg_3892_);
lean_dec_ref_known(v_x_3888_, 2);
v_zero_3893_ = lean_unsigned_to_nat(0u);
v_isZero_3894_ = lean_nat_dec_eq(v_x_3890_, v_zero_3893_);
if (v_isZero_3894_ == 0)
{
lean_object* v_one_3895_; lean_object* v_n_3896_; lean_object* v___x_3897_; 
v_one_3895_ = lean_unsigned_to_nat(1u);
v_n_3896_ = lean_nat_sub(v_x_3890_, v_one_3895_);
lean_dec(v_x_3890_);
v___x_3897_ = lean_array_set(v_x_3889_, v_n_3896_, v_arg_3892_);
v_x_3888_ = v_fn_3891_;
v_x_3889_ = v___x_3897_;
v_x_3890_ = v_n_3896_;
goto _start;
}
else
{
lean_dec_ref(v_arg_3892_);
lean_dec_ref(v_fn_3891_);
lean_dec(v_x_3890_);
return v_x_3889_;
}
}
else
{
lean_dec(v_x_3890_);
lean_dec_ref(v_x_3888_);
return v_x_3889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getBoundedAppArgs(lean_object* v_maxArgs_3899_, lean_object* v_e_3900_){
_start:
{
lean_object* v_dummy_3901_; lean_object* v___y_3903_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_dummy_3901_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v___x_3906_ = l_Lean_Expr_getAppNumArgs(v_e_3900_);
v___x_3907_ = lean_nat_dec_le(v_maxArgs_3899_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_dec(v_maxArgs_3899_);
v___y_3903_ = v___x_3906_;
goto v___jp_3902_;
}
else
{
lean_dec(v___x_3906_);
v___y_3903_ = v_maxArgs_3899_;
goto v___jp_3902_;
}
v___jp_3902_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_inc(v___y_3903_);
v___x_3904_ = lean_mk_array(v___y_3903_, v_dummy_3901_);
v___x_3905_ = l___private_Lean_Expr_0__Lean_Expr_getBoundedAppArgsAux(v_e_3900_, v___x_3904_, v___y_3903_);
return v___x_3905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
if (lean_obj_tag(v_x_3908_) == 5)
{
lean_object* v_fn_3910_; lean_object* v_arg_3911_; lean_object* v___x_3912_; 
v_fn_3910_ = lean_ctor_get(v_x_3908_, 0);
lean_inc_ref(v_fn_3910_);
v_arg_3911_ = lean_ctor_get(v_x_3908_, 1);
lean_inc_ref(v_arg_3911_);
lean_dec_ref_known(v_x_3908_, 2);
v___x_3912_ = lean_array_push(v_x_3909_, v_arg_3911_);
v_x_3908_ = v_fn_3910_;
v_x_3909_ = v___x_3912_;
goto _start;
}
else
{
lean_dec_ref(v_x_3908_);
return v_x_3909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* v_e_3914_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3915_ = l_Lean_Expr_getAppNumArgs(v_e_3914_);
v___x_3916_ = lean_mk_empty_array_with_capacity(v___x_3915_);
lean_dec(v___x_3915_);
v___x_3917_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3914_, v___x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___redArg(lean_object* v_k_3918_, lean_object* v_x_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_){
_start:
{
if (lean_obj_tag(v_x_3919_) == 5)
{
lean_object* v_fn_3922_; lean_object* v_arg_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_fn_3922_ = lean_ctor_get(v_x_3919_, 0);
lean_inc_ref(v_fn_3922_);
v_arg_3923_ = lean_ctor_get(v_x_3919_, 1);
lean_inc_ref(v_arg_3923_);
lean_dec_ref_known(v_x_3919_, 2);
v___x_3924_ = lean_array_set(v_x_3920_, v_x_3921_, v_arg_3923_);
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_nat_sub(v_x_3921_, v___x_3925_);
lean_dec(v_x_3921_);
v_x_3919_ = v_fn_3922_;
v_x_3920_ = v___x_3924_;
v_x_3921_ = v___x_3926_;
goto _start;
}
else
{
lean_object* v___x_3928_; 
lean_dec(v_x_3921_);
v___x_3928_ = lean_apply_2(v_k_3918_, v_x_3919_, v_x_3920_);
return v___x_3928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* v_00_u03b1_3929_, lean_object* v_k_3930_, lean_object* v_x_3931_, lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Expr_withAppAux___redArg(v_k_3930_, v_x_3931_, v_x_3932_, v_x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___redArg(lean_object* v_e_3935_, lean_object* v_k_3936_){
_start:
{
lean_object* v_dummy_3937_; lean_object* v_nargs_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_dummy_3937_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3938_ = l_Lean_Expr_getAppNumArgs(v_e_3935_);
lean_inc(v_nargs_3938_);
v___x_3939_ = lean_mk_array(v_nargs_3938_, v_dummy_3937_);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_sub(v_nargs_3938_, v___x_3940_);
lean_dec(v_nargs_3938_);
v___x_3942_ = l_Lean_Expr_withAppAux___redArg(v_k_3936_, v_e_3935_, v___x_3939_, v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* v_00_u03b1_3943_, lean_object* v_e_3944_, lean_object* v_k_3945_){
_start:
{
lean_object* v_dummy_3946_; lean_object* v_nargs_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_dummy_3946_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3947_ = l_Lean_Expr_getAppNumArgs(v_e_3944_);
lean_inc(v_nargs_3947_);
v___x_3948_ = lean_mk_array(v_nargs_3947_, v_dummy_3946_);
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = lean_nat_sub(v_nargs_3947_, v___x_3949_);
lean_dec(v_nargs_3947_);
v___x_3951_ = l_Lean_Expr_withAppAux___redArg(v_k_3945_, v_e_3944_, v___x_3948_, v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(lean_object* v_x_3952_, lean_object* v_x_3953_, lean_object* v_x_3954_){
_start:
{
if (lean_obj_tag(v_x_3952_) == 5)
{
lean_object* v_fn_3955_; lean_object* v_arg_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_fn_3955_ = lean_ctor_get(v_x_3952_, 0);
lean_inc_ref(v_fn_3955_);
v_arg_3956_ = lean_ctor_get(v_x_3952_, 1);
lean_inc_ref(v_arg_3956_);
lean_dec_ref_known(v_x_3952_, 2);
v___x_3957_ = lean_array_set(v_x_3953_, v_x_3954_, v_arg_3956_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_sub(v_x_3954_, v___x_3958_);
lean_dec(v_x_3954_);
v_x_3952_ = v_fn_3955_;
v_x_3953_ = v___x_3957_;
v_x_3954_ = v___x_3959_;
goto _start;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec(v_x_3954_);
v___x_3961_ = l_Lean_Expr_constName(v_x_3952_);
lean_dec_ref(v_x_3952_);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v_x_3953_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFnArgs(lean_object* v_e_3963_){
_start:
{
lean_object* v_dummy_3964_; lean_object* v_nargs_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_dummy_3964_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_3965_ = l_Lean_Expr_getAppNumArgs(v_e_3963_);
lean_inc(v_nargs_3965_);
v___x_3966_ = lean_mk_array(v_nargs_3965_, v_dummy_3964_);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_sub(v_nargs_3965_, v___x_3967_);
lean_dec(v_nargs_3965_);
v___x_3969_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_getAppFnArgs_spec__0(v_e_3963_, v___x_3966_, v___x_3968_);
return v___x_3969_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Array_instInhabited___redArg();
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(lean_object* v_msg_3971_){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_obj_once(&l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0___closed__0);
v___x_3973_ = lean_panic_fn_borrowed(v___x_3972_, v_msg_3971_);
return v___x_3973_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3976_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__1));
v___x_3977_ = lean_unsigned_to_nat(27u);
v___x_3978_ = lean_unsigned_to_nat(1282u);
v___x_3979_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__0));
v___x_3980_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_3981_ = l_mkPanicMessageWithDecl(v___x_3980_, v___x_3979_, v___x_3978_, v___x_3977_, v___x_3976_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_zero_3985_; uint8_t v_isZero_3986_; 
v_zero_3985_ = lean_unsigned_to_nat(0u);
v_isZero_3986_ = lean_nat_dec_eq(v_a_3982_, v_zero_3985_);
if (v_isZero_3986_ == 1)
{
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
return v_a_3984_;
}
else
{
if (lean_obj_tag(v_a_3983_) == 5)
{
lean_object* v_fn_3987_; lean_object* v_arg_3988_; lean_object* v_one_3989_; lean_object* v_n_3990_; lean_object* v___x_3991_; 
v_fn_3987_ = lean_ctor_get(v_a_3983_, 0);
lean_inc_ref(v_fn_3987_);
v_arg_3988_ = lean_ctor_get(v_a_3983_, 1);
lean_inc_ref(v_arg_3988_);
lean_dec_ref_known(v_a_3983_, 2);
v_one_3989_ = lean_unsigned_to_nat(1u);
v_n_3990_ = lean_nat_sub(v_a_3982_, v_one_3989_);
lean_dec(v_a_3982_);
v___x_3991_ = lean_array_set(v_a_3984_, v_n_3990_, v_arg_3988_);
v_a_3982_ = v_n_3990_;
v_a_3983_ = v_fn_3987_;
v_a_3984_ = v___x_3991_;
goto _start;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
v___x_3993_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2, &l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop___closed__2);
v___x_3994_ = l_panic___at___00__private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop_spec__0(v___x_3993_);
return v___x_3994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgsN(lean_object* v_e_3995_, lean_object* v_n_3996_){
_start:
{
lean_object* v_dummy_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_dummy_3997_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
lean_inc(v_n_3996_);
v___x_3998_ = lean_mk_array(v_n_3996_, v_dummy_3997_);
v___x_3999_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_n_3996_, v_e_3995_, v___x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN(lean_object* v_e_4000_, lean_object* v_n_4001_){
_start:
{
lean_object* v_zero_4002_; uint8_t v_isZero_4003_; 
v_zero_4002_ = lean_unsigned_to_nat(0u);
v_isZero_4003_ = lean_nat_dec_eq(v_n_4001_, v_zero_4002_);
if (v_isZero_4003_ == 1)
{
lean_dec(v_n_4001_);
lean_inc_ref(v_e_4000_);
return v_e_4000_;
}
else
{
if (lean_obj_tag(v_e_4000_) == 5)
{
lean_object* v_fn_4004_; lean_object* v_one_4005_; lean_object* v_n_4006_; 
v_fn_4004_ = lean_ctor_get(v_e_4000_, 0);
v_one_4005_ = lean_unsigned_to_nat(1u);
v_n_4006_ = lean_nat_sub(v_n_4001_, v_one_4005_);
lean_dec(v_n_4001_);
v_e_4000_ = v_fn_4004_;
v_n_4001_ = v_n_4006_;
goto _start;
}
else
{
lean_dec(v_n_4001_);
lean_inc_ref(v_e_4000_);
return v_e_4000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_stripArgsN___boxed(lean_object* v_e_4008_, lean_object* v_n_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_Expr_stripArgsN(v_e_4008_, v_n_4009_);
lean_dec_ref(v_e_4008_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix(lean_object* v_e_4011_, lean_object* v_n_4012_){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4013_ = l_Lean_Expr_getAppNumArgs(v_e_4011_);
v___x_4014_ = lean_nat_sub(v___x_4013_, v_n_4012_);
lean_dec(v___x_4013_);
v___x_4015_ = l_Lean_Expr_stripArgsN(v_e_4011_, v___x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppPrefix___boxed(lean_object* v_e_4016_, lean_object* v_n_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Expr_getAppPrefix(v_e_4016_, v_n_4017_);
lean_dec(v_n_4017_);
lean_dec_ref(v_e_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__0(lean_object* v_args_4019_, lean_object* v_inst_4020_, lean_object* v_f_4021_, lean_object* v_x_4022_){
_start:
{
size_t v_sz_4023_; size_t v___x_4024_; lean_object* v___x_4025_; 
v_sz_4023_ = lean_array_size(v_args_4019_);
v___x_4024_ = ((size_t)0ULL);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4020_, v_f_4021_, v_sz_4023_, v___x_4024_, v_args_4019_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg___lam__1(lean_object* v_toFunctor_4027_, lean_object* v_inst_4028_, lean_object* v_f_4029_, lean_object* v_toSeq_4030_, lean_object* v_fn_4031_, lean_object* v_args_4032_){
_start:
{
lean_object* v_map_4033_; lean_object* v___f_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v_map_4033_ = lean_ctor_get(v_toFunctor_4027_, 0);
lean_inc(v_map_4033_);
lean_dec_ref(v_toFunctor_4027_);
lean_inc(v_f_4029_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4034_, 0, v_args_4032_);
lean_closure_set(v___f_4034_, 1, v_inst_4028_);
lean_closure_set(v___f_4034_, 2, v_f_4029_);
v___x_4035_ = ((lean_object*)(l_Lean_Expr_traverseApp___redArg___lam__1___closed__0));
v___x_4036_ = lean_apply_1(v_f_4029_, v_fn_4031_);
v___x_4037_ = lean_apply_4(v_map_4033_, lean_box(0), lean_box(0), v___x_4035_, v___x_4036_);
v___x_4038_ = lean_apply_4(v_toSeq_4030_, lean_box(0), lean_box(0), v___x_4037_, v___f_4034_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___redArg(lean_object* v_inst_4039_, lean_object* v_f_4040_, lean_object* v_e_4041_){
_start:
{
lean_object* v_toApplicative_4042_; lean_object* v_toFunctor_4043_; lean_object* v_toSeq_4044_; lean_object* v___f_4045_; lean_object* v_dummy_4046_; lean_object* v_nargs_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_toApplicative_4042_ = lean_ctor_get(v_inst_4039_, 0);
v_toFunctor_4043_ = lean_ctor_get(v_toApplicative_4042_, 0);
lean_inc_ref(v_toFunctor_4043_);
v_toSeq_4044_ = lean_ctor_get(v_toApplicative_4042_, 2);
lean_inc(v_toSeq_4044_);
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___redArg___lam__1), 6, 4);
lean_closure_set(v___f_4045_, 0, v_toFunctor_4043_);
lean_closure_set(v___f_4045_, 1, v_inst_4039_);
lean_closure_set(v___f_4045_, 2, v_f_4040_);
lean_closure_set(v___f_4045_, 3, v_toSeq_4044_);
v_dummy_4046_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_4047_ = l_Lean_Expr_getAppNumArgs(v_e_4041_);
lean_inc(v_nargs_4047_);
v___x_4048_ = lean_mk_array(v_nargs_4047_, v_dummy_4046_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_sub(v_nargs_4047_, v___x_4049_);
lean_dec(v_nargs_4047_);
v___x_4051_ = l_Lean_Expr_withAppAux___redArg(v___f_4045_, v_e_4041_, v___x_4048_, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* v_M_4052_, lean_object* v_inst_4053_, lean_object* v_f_4054_, lean_object* v_e_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Expr_traverseApp___redArg(v_inst_4053_, v_f_4054_, v_e_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(lean_object* v_k_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_){
_start:
{
if (lean_obj_tag(v_x_4058_) == 5)
{
lean_object* v_fn_4060_; lean_object* v_arg_4061_; lean_object* v___x_4062_; 
v_fn_4060_ = lean_ctor_get(v_x_4058_, 0);
lean_inc_ref(v_fn_4060_);
v_arg_4061_ = lean_ctor_get(v_x_4058_, 1);
lean_inc_ref(v_arg_4061_);
lean_dec_ref_known(v_x_4058_, 2);
v___x_4062_ = lean_array_push(v_x_4059_, v_arg_4061_);
v_x_4058_ = v_fn_4060_;
v_x_4059_ = v___x_4062_;
goto _start;
}
else
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_apply_2(v_k_4057_, v_x_4058_, v_x_4059_);
return v___x_4064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* v_00_u03b1_4065_, lean_object* v_k_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4066_, v_x_4067_, v_x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___redArg(lean_object* v_e_4070_, lean_object* v_k_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = l_Lean_Expr_getAppNumArgs(v_e_4070_);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_4072_);
lean_dec(v___x_4072_);
v___x_4074_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4071_, v_e_4070_, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* v_00_u03b1_4075_, lean_object* v_e_4076_, lean_object* v_k_4077_){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = l_Lean_Expr_getAppNumArgs(v_e_4076_);
v___x_4079_ = lean_mk_empty_array_with_capacity(v___x_4078_);
lean_dec(v___x_4078_);
v___x_4080_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___redArg(v_k_4077_, v_e_4076_, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* v_x_4081_, lean_object* v_x_4082_, lean_object* v_x_4083_){
_start:
{
if (lean_obj_tag(v_x_4081_) == 5)
{
lean_object* v_fn_4084_; lean_object* v_arg_4085_; lean_object* v_zero_4086_; uint8_t v_isZero_4087_; 
v_fn_4084_ = lean_ctor_get(v_x_4081_, 0);
v_arg_4085_ = lean_ctor_get(v_x_4081_, 1);
v_zero_4086_ = lean_unsigned_to_nat(0u);
v_isZero_4087_ = lean_nat_dec_eq(v_x_4082_, v_zero_4086_);
if (v_isZero_4087_ == 1)
{
lean_dec(v_x_4082_);
lean_inc_ref(v_arg_4085_);
return v_arg_4085_;
}
else
{
lean_object* v_one_4088_; lean_object* v_n_4089_; 
v_one_4088_ = lean_unsigned_to_nat(1u);
v_n_4089_ = lean_nat_sub(v_x_4082_, v_one_4088_);
lean_dec(v_x_4082_);
v_x_4081_ = v_fn_4084_;
v_x_4082_ = v_n_4089_;
goto _start;
}
}
else
{
lean_dec(v_x_4082_);
lean_inc_ref(v_x_4083_);
return v_x_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* v_x_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_Expr_getRevArgD(v_x_4091_, v_x_4092_, v_x_4093_);
lean_dec_ref(v_x_4093_);
lean_dec_ref(v_x_4091_);
return v_res_4094_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4097_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4098_ = lean_unsigned_to_nat(20u);
v___x_4099_ = lean_unsigned_to_nat(1323u);
v___x_4100_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__0));
v___x_4101_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4102_ = l_mkPanicMessageWithDecl(v___x_4101_, v___x_4100_, v___x_4099_, v___x_4098_, v___x_4097_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* v_x_4103_, lean_object* v_x_4104_){
_start:
{
if (lean_obj_tag(v_x_4103_) == 5)
{
lean_object* v_fn_4105_; lean_object* v_arg_4106_; lean_object* v_zero_4107_; uint8_t v_isZero_4108_; 
v_fn_4105_ = lean_ctor_get(v_x_4103_, 0);
v_arg_4106_ = lean_ctor_get(v_x_4103_, 1);
v_zero_4107_ = lean_unsigned_to_nat(0u);
v_isZero_4108_ = lean_nat_dec_eq(v_x_4104_, v_zero_4107_);
if (v_isZero_4108_ == 1)
{
lean_dec(v_x_4104_);
lean_inc_ref(v_arg_4106_);
return v_arg_4106_;
}
else
{
lean_object* v_one_4109_; lean_object* v_n_4110_; 
v_one_4109_ = lean_unsigned_to_nat(1u);
v_n_4110_ = lean_nat_sub(v_x_4104_, v_one_4109_);
lean_dec(v_x_4104_);
v_x_4103_ = v_fn_4105_;
v_x_4104_ = v_n_4110_;
goto _start;
}
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec(v_x_4104_);
v___x_4112_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21___closed__2, &l_Lean_Expr_getRevArg_x21___closed__2_once, _init_l_Lean_Expr_getRevArg_x21___closed__2);
v___x_4113_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4112_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* v_x_4114_, lean_object* v_x_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Expr_getRevArg_x21(v_x_4114_, v_x_4115_);
lean_dec_ref(v_x_4114_);
return v_res_4116_;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21_x27___closed__1(void){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4118_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21___closed__1));
v___x_4119_ = lean_unsigned_to_nat(20u);
v___x_4120_ = lean_unsigned_to_nat(1330u);
v___x_4121_ = ((lean_object*)(l_Lean_Expr_getRevArg_x21_x27___closed__0));
v___x_4122_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_4123_ = l_mkPanicMessageWithDecl(v___x_4122_, v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27(lean_object* v_x_4124_, lean_object* v_x_4125_){
_start:
{
switch(lean_obj_tag(v_x_4124_))
{
case 10:
{
lean_object* v_expr_4126_; 
v_expr_4126_ = lean_ctor_get(v_x_4124_, 1);
v_x_4124_ = v_expr_4126_;
goto _start;
}
case 5:
{
lean_object* v_fn_4128_; lean_object* v_arg_4129_; lean_object* v_zero_4130_; uint8_t v_isZero_4131_; 
v_fn_4128_ = lean_ctor_get(v_x_4124_, 0);
v_arg_4129_ = lean_ctor_get(v_x_4124_, 1);
v_zero_4130_ = lean_unsigned_to_nat(0u);
v_isZero_4131_ = lean_nat_dec_eq(v_x_4125_, v_zero_4130_);
if (v_isZero_4131_ == 1)
{
lean_dec(v_x_4125_);
lean_inc_ref(v_arg_4129_);
return v_arg_4129_;
}
else
{
lean_object* v_one_4132_; lean_object* v_n_4133_; 
v_one_4132_ = lean_unsigned_to_nat(1u);
v_n_4133_ = lean_nat_sub(v_x_4125_, v_one_4132_);
lean_dec(v_x_4125_);
v_x_4124_ = v_fn_4128_;
v_x_4125_ = v_n_4133_;
goto _start;
}
}
default: 
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec(v_x_4125_);
v___x_4135_ = lean_obj_once(&l_Lean_Expr_getRevArg_x21_x27___closed__1, &l_Lean_Expr_getRevArg_x21_x27___closed__1_once, _init_l_Lean_Expr_getRevArg_x21_x27___closed__1);
v___x_4136_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_4135_);
return v___x_4136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21_x27___boxed(lean_object* v_x_4137_, lean_object* v_x_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Expr_getRevArg_x21_x27(v_x_4137_, v_x_4138_);
lean_dec_ref(v_x_4137_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* v_e_4140_, lean_object* v_i_4141_, lean_object* v_n_4142_){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4143_ = lean_nat_sub(v_n_4142_, v_i_4141_);
v___x_4144_ = lean_unsigned_to_nat(1u);
v___x_4145_ = lean_nat_sub(v___x_4143_, v___x_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = l_Lean_Expr_getRevArg_x21(v_e_4140_, v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* v_e_4147_, lean_object* v_i_4148_, lean_object* v_n_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_Expr_getArg_x21(v_e_4147_, v_i_4148_, v_n_4149_);
lean_dec(v_n_4149_);
lean_dec(v_i_4148_);
lean_dec_ref(v_e_4147_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27(lean_object* v_e_4151_, lean_object* v_i_4152_, lean_object* v_n_4153_){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = lean_nat_sub(v_n_4153_, v_i_4152_);
v___x_4155_ = lean_unsigned_to_nat(1u);
v___x_4156_ = lean_nat_sub(v___x_4154_, v___x_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = l_Lean_Expr_getRevArg_x21_x27(v_e_4151_, v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21_x27___boxed(lean_object* v_e_4158_, lean_object* v_i_4159_, lean_object* v_n_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Expr_getArg_x21_x27(v_e_4158_, v_i_4159_, v_n_4160_);
lean_dec(v_n_4160_);
lean_dec(v_i_4159_);
lean_dec_ref(v_e_4158_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* v_e_4162_, lean_object* v_i_4163_, lean_object* v_v_u2080_4164_, lean_object* v_n_4165_){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4166_ = lean_nat_sub(v_n_4165_, v_i_4163_);
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = lean_nat_sub(v___x_4166_, v___x_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = l_Lean_Expr_getRevArgD(v_e_4162_, v___x_4168_, v_v_u2080_4164_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* v_e_4170_, lean_object* v_i_4171_, lean_object* v_v_u2080_4172_, lean_object* v_n_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Expr_getArgD(v_e_4170_, v_i_4171_, v_v_u2080_4172_, v_n_4173_);
lean_dec(v_n_4173_);
lean_dec_ref(v_v_u2080_4172_);
lean_dec(v_i_4171_);
lean_dec_ref(v_e_4170_);
return v_res_4174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* v_e_4175_){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; uint8_t v___x_4178_; 
v___x_4176_ = lean_unsigned_to_nat(0u);
v___x_4177_ = l_Lean_Expr_looseBVarRange(v_e_4175_);
v___x_4178_ = lean_nat_dec_lt(v___x_4176_, v___x_4177_);
lean_dec(v___x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* v_e_4179_){
_start:
{
uint8_t v_res_4180_; lean_object* v_r_4181_; 
v_res_4180_ = l_Lean_Expr_hasLooseBVars(v_e_4179_);
lean_dec_ref(v_e_4179_);
v_r_4181_ = lean_box(v_res_4180_);
return v_r_4181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* v_e_4182_){
_start:
{
if (lean_obj_tag(v_e_4182_) == 7)
{
lean_object* v_body_4183_; uint8_t v___x_4184_; 
v_body_4183_ = lean_ctor_get(v_e_4182_, 2);
v___x_4184_ = l_Lean_Expr_hasLooseBVars(v_body_4183_);
if (v___x_4184_ == 0)
{
uint8_t v___x_4185_; 
v___x_4185_ = 1;
return v___x_4185_;
}
else
{
uint8_t v___x_4186_; 
v___x_4186_ = 0;
return v___x_4186_;
}
}
else
{
uint8_t v___x_4187_; 
v___x_4187_ = 0;
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* v_e_4188_){
_start:
{
uint8_t v_res_4189_; lean_object* v_r_4190_; 
v_res_4189_ = l_Lean_Expr_isArrow(v_e_4188_);
lean_dec_ref(v_e_4188_);
v_r_4190_ = lean_box(v_res_4189_);
return v_r_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* v_e_4193_, lean_object* v_bvarIdx_4194_){
_start:
{
uint8_t v_res_4195_; lean_object* v_r_4196_; 
v_res_4195_ = lean_expr_has_loose_bvar(v_e_4193_, v_bvarIdx_4194_);
lean_dec(v_bvarIdx_4194_);
lean_dec_ref(v_e_4193_);
v_r_4196_ = lean_box(v_res_4195_);
return v_r_4196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* v_e_4197_, lean_object* v_bvarIdx_4198_, uint8_t v_considerRange_4199_){
_start:
{
if (lean_obj_tag(v_e_4197_) == 7)
{
lean_object* v_binderType_4200_; lean_object* v_body_4201_; uint8_t v_binderInfo_4202_; uint8_t v___x_4207_; 
v_binderType_4200_ = lean_ctor_get(v_e_4197_, 1);
v_body_4201_ = lean_ctor_get(v_e_4197_, 2);
v_binderInfo_4202_ = lean_ctor_get_uint8(v_e_4197_, sizeof(void*)*3 + 8);
v___x_4207_ = lean_expr_has_loose_bvar(v_binderType_4200_, v_bvarIdx_4198_);
if (v___x_4207_ == 0)
{
goto v___jp_4203_;
}
else
{
uint8_t v___x_4208_; 
v___x_4208_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4202_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_body_4201_, v___x_4209_, v_considerRange_4199_);
if (v___x_4210_ == 0)
{
goto v___jp_4203_;
}
else
{
lean_dec(v_bvarIdx_4198_);
return v___x_4210_;
}
}
else
{
lean_dec(v_bvarIdx_4198_);
return v___x_4208_;
}
}
v___jp_4203_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_unsigned_to_nat(1u);
v___x_4205_ = lean_nat_add(v_bvarIdx_4198_, v___x_4204_);
lean_dec(v_bvarIdx_4198_);
v_e_4197_ = v_body_4201_;
v_bvarIdx_4198_ = v___x_4205_;
goto _start;
}
}
else
{
if (v_considerRange_4199_ == 0)
{
lean_dec(v_bvarIdx_4198_);
return v_considerRange_4199_;
}
else
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_expr_has_loose_bvar(v_e_4197_, v_bvarIdx_4198_);
lean_dec(v_bvarIdx_4198_);
return v___x_4211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* v_e_4212_, lean_object* v_bvarIdx_4213_, lean_object* v_considerRange_4214_){
_start:
{
uint8_t v_considerRange_boxed_4215_; uint8_t v_res_4216_; lean_object* v_r_4217_; 
v_considerRange_boxed_4215_ = lean_unbox(v_considerRange_4214_);
v_res_4216_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_e_4212_, v_bvarIdx_4213_, v_considerRange_boxed_4215_);
lean_dec_ref(v_e_4212_);
v_r_4217_ = lean_box(v_res_4216_);
return v_r_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* v_e_4221_, lean_object* v_s_4222_, lean_object* v_d_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = lean_expr_lower_loose_bvars(v_e_4221_, v_s_4222_, v_d_4223_);
lean_dec(v_d_4223_);
lean_dec(v_s_4222_);
lean_dec_ref(v_e_4221_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* v_e_4228_, lean_object* v_s_4229_, lean_object* v_d_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = lean_expr_lift_loose_bvars(v_e_4228_, v_s_4229_, v_d_4230_);
lean_dec(v_d_4230_);
lean_dec(v_s_4229_);
lean_dec_ref(v_e_4228_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* v_e_4232_, lean_object* v_numParams_4233_, uint8_t v_considerRange_4234_){
_start:
{
if (lean_obj_tag(v_e_4232_) == 7)
{
lean_object* v_binderName_4235_; lean_object* v_binderType_4236_; lean_object* v_body_4237_; uint8_t v_binderInfo_4238_; lean_object* v_zero_4239_; uint8_t v_isZero_4240_; 
v_binderName_4235_ = lean_ctor_get(v_e_4232_, 0);
v_binderType_4236_ = lean_ctor_get(v_e_4232_, 1);
v_body_4237_ = lean_ctor_get(v_e_4232_, 2);
v_binderInfo_4238_ = lean_ctor_get_uint8(v_e_4232_, sizeof(void*)*3 + 8);
v_zero_4239_ = lean_unsigned_to_nat(0u);
v_isZero_4240_ = lean_nat_dec_eq(v_numParams_4233_, v_zero_4239_);
if (v_isZero_4240_ == 0)
{
lean_object* v_one_4241_; lean_object* v_n_4242_; lean_object* v_b_4243_; uint8_t v___x_4244_; 
lean_inc_ref(v_body_4237_);
lean_inc_ref(v_binderType_4236_);
lean_inc(v_binderName_4235_);
lean_dec_ref_known(v_e_4232_, 3);
v_one_4241_ = lean_unsigned_to_nat(1u);
v_n_4242_ = lean_nat_sub(v_numParams_4233_, v_one_4241_);
v_b_4243_ = l_Lean_Expr_inferImplicit(v_body_4237_, v_n_4242_, v_considerRange_4234_);
lean_dec(v_n_4242_);
v___x_4244_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_4238_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Expr_forallE___override(v_binderName_4235_, v_binderType_4236_, v_b_4243_, v_binderInfo_4238_);
return v___x_4245_;
}
else
{
uint8_t v___x_4246_; 
v___x_4246_ = l_Lean_Expr_hasLooseBVarInExplicitDomain(v_b_4243_, v_zero_4239_, v_considerRange_4234_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Expr_forallE___override(v_binderName_4235_, v_binderType_4236_, v_b_4243_, v_binderInfo_4238_);
return v___x_4247_;
}
else
{
uint8_t v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = 1;
v___x_4249_ = l_Lean_Expr_forallE___override(v_binderName_4235_, v_binderType_4236_, v_b_4243_, v___x_4248_);
return v___x_4249_;
}
}
}
else
{
return v_e_4232_;
}
}
else
{
return v_e_4232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* v_e_4250_, lean_object* v_numParams_4251_, lean_object* v_considerRange_4252_){
_start:
{
uint8_t v_considerRange_boxed_4253_; lean_object* v_res_4254_; 
v_considerRange_boxed_4253_ = lean_unbox(v_considerRange_4252_);
v_res_4254_ = l_Lean_Expr_inferImplicit(v_e_4250_, v_numParams_4251_, v_considerRange_boxed_4253_);
lean_dec(v_numParams_4251_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object* v_e_4255_, lean_object* v_binderInfos_x3f_4256_){
_start:
{
if (lean_obj_tag(v_e_4255_) == 7)
{
if (lean_obj_tag(v_binderInfos_x3f_4256_) == 1)
{
lean_object* v_binderName_4257_; lean_object* v_binderType_4258_; lean_object* v_body_4259_; uint8_t v_binderInfo_4260_; lean_object* v_head_4261_; lean_object* v_tail_4262_; lean_object* v_b_4263_; 
v_binderName_4257_ = lean_ctor_get(v_e_4255_, 0);
lean_inc(v_binderName_4257_);
v_binderType_4258_ = lean_ctor_get(v_e_4255_, 1);
lean_inc_ref(v_binderType_4258_);
v_body_4259_ = lean_ctor_get(v_e_4255_, 2);
lean_inc_ref(v_body_4259_);
v_binderInfo_4260_ = lean_ctor_get_uint8(v_e_4255_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4255_, 3);
v_head_4261_ = lean_ctor_get(v_binderInfos_x3f_4256_, 0);
v_tail_4262_ = lean_ctor_get(v_binderInfos_x3f_4256_, 1);
v_b_4263_ = l_Lean_Expr_updateForallBinderInfos(v_body_4259_, v_tail_4262_);
if (lean_obj_tag(v_head_4261_) == 0)
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Expr_forallE___override(v_binderName_4257_, v_binderType_4258_, v_b_4263_, v_binderInfo_4260_);
return v___x_4264_;
}
else
{
lean_object* v_val_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; 
v_val_4265_ = lean_ctor_get(v_head_4261_, 0);
v___x_4266_ = lean_unbox(v_val_4265_);
v___x_4267_ = l_Lean_Expr_forallE___override(v_binderName_4257_, v_binderType_4258_, v_b_4263_, v___x_4266_);
return v___x_4267_;
}
}
else
{
return v_e_4255_;
}
}
else
{
return v_e_4255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallBinderInfos___boxed(lean_object* v_e_4268_, lean_object* v_binderInfos_x3f_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_Expr_updateForallBinderInfos(v_e_4268_, v_binderInfos_x3f_4269_);
lean_dec(v_binderInfos_x3f_4269_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateBinderNames(lean_object* v_e_4271_, lean_object* v_binderNames_x3f_4272_){
_start:
{
switch(lean_obj_tag(v_e_4271_))
{
case 7:
{
if (lean_obj_tag(v_binderNames_x3f_4272_) == 1)
{
lean_object* v_binderName_4273_; lean_object* v_binderType_4274_; lean_object* v_body_4275_; uint8_t v_binderInfo_4276_; lean_object* v_head_4277_; lean_object* v_tail_4278_; lean_object* v_b_4279_; 
v_binderName_4273_ = lean_ctor_get(v_e_4271_, 0);
lean_inc(v_binderName_4273_);
v_binderType_4274_ = lean_ctor_get(v_e_4271_, 1);
lean_inc_ref(v_binderType_4274_);
v_body_4275_ = lean_ctor_get(v_e_4271_, 2);
lean_inc_ref(v_body_4275_);
v_binderInfo_4276_ = lean_ctor_get_uint8(v_e_4271_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4271_, 3);
v_head_4277_ = lean_ctor_get(v_binderNames_x3f_4272_, 0);
lean_inc(v_head_4277_);
v_tail_4278_ = lean_ctor_get(v_binderNames_x3f_4272_, 1);
lean_inc(v_tail_4278_);
lean_dec_ref_known(v_binderNames_x3f_4272_, 2);
v_b_4279_ = l_Lean_Expr_updateBinderNames(v_body_4275_, v_tail_4278_);
if (lean_obj_tag(v_head_4277_) == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Expr_forallE___override(v_binderName_4273_, v_binderType_4274_, v_b_4279_, v_binderInfo_4276_);
return v___x_4280_;
}
else
{
lean_object* v_val_4281_; lean_object* v___x_4282_; 
lean_dec(v_binderName_4273_);
v_val_4281_ = lean_ctor_get(v_head_4277_, 0);
lean_inc(v_val_4281_);
lean_dec_ref_known(v_head_4277_, 1);
v___x_4282_ = l_Lean_Expr_forallE___override(v_val_4281_, v_binderType_4274_, v_b_4279_, v_binderInfo_4276_);
return v___x_4282_;
}
}
else
{
lean_dec(v_binderNames_x3f_4272_);
return v_e_4271_;
}
}
case 6:
{
if (lean_obj_tag(v_binderNames_x3f_4272_) == 1)
{
lean_object* v_binderName_4283_; lean_object* v_binderType_4284_; lean_object* v_body_4285_; uint8_t v_binderInfo_4286_; lean_object* v_head_4287_; lean_object* v_tail_4288_; lean_object* v_b_4289_; 
v_binderName_4283_ = lean_ctor_get(v_e_4271_, 0);
lean_inc(v_binderName_4283_);
v_binderType_4284_ = lean_ctor_get(v_e_4271_, 1);
lean_inc_ref(v_binderType_4284_);
v_body_4285_ = lean_ctor_get(v_e_4271_, 2);
lean_inc_ref(v_body_4285_);
v_binderInfo_4286_ = lean_ctor_get_uint8(v_e_4271_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4271_, 3);
v_head_4287_ = lean_ctor_get(v_binderNames_x3f_4272_, 0);
lean_inc(v_head_4287_);
v_tail_4288_ = lean_ctor_get(v_binderNames_x3f_4272_, 1);
lean_inc(v_tail_4288_);
lean_dec_ref_known(v_binderNames_x3f_4272_, 2);
v_b_4289_ = l_Lean_Expr_updateBinderNames(v_body_4285_, v_tail_4288_);
if (lean_obj_tag(v_head_4287_) == 0)
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Expr_lam___override(v_binderName_4283_, v_binderType_4284_, v_b_4289_, v_binderInfo_4286_);
return v___x_4290_;
}
else
{
lean_object* v_val_4291_; lean_object* v___x_4292_; 
lean_dec(v_binderName_4283_);
v_val_4291_ = lean_ctor_get(v_head_4287_, 0);
lean_inc(v_val_4291_);
lean_dec_ref_known(v_head_4287_, 1);
v___x_4292_ = l_Lean_Expr_lam___override(v_val_4291_, v_binderType_4284_, v_b_4289_, v_binderInfo_4286_);
return v___x_4292_;
}
}
else
{
lean_dec(v_binderNames_x3f_4272_);
return v_e_4271_;
}
}
default: 
{
lean_dec(v_binderNames_x3f_4272_);
return v_e_4271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* v_e_4295_, lean_object* v_subst_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = lean_expr_instantiate(v_e_4295_, v_subst_4296_);
lean_dec_ref(v_subst_4296_);
lean_dec_ref(v_e_4295_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* v_e_4300_, lean_object* v_subst_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = lean_expr_instantiate1(v_e_4300_, v_subst_4301_);
lean_dec_ref(v_subst_4301_);
lean_dec_ref(v_e_4300_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* v_e_4305_, lean_object* v_subst_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = lean_expr_instantiate_rev(v_e_4305_, v_subst_4306_);
lean_dec_ref(v_subst_4306_);
lean_dec_ref(v_e_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* v_e_4312_, lean_object* v_beginIdx_4313_, lean_object* v_endIdx_4314_, lean_object* v_subst_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = lean_expr_instantiate_range(v_e_4312_, v_beginIdx_4313_, v_endIdx_4314_, v_subst_4315_);
lean_dec_ref(v_subst_4315_);
lean_dec(v_endIdx_4314_);
lean_dec(v_beginIdx_4313_);
lean_dec_ref(v_e_4312_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* v_e_4321_, lean_object* v_beginIdx_4322_, lean_object* v_endIdx_4323_, lean_object* v_subst_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = lean_expr_instantiate_rev_range(v_e_4321_, v_beginIdx_4322_, v_endIdx_4323_, v_subst_4324_);
lean_dec_ref(v_subst_4324_);
lean_dec(v_endIdx_4323_);
lean_dec(v_beginIdx_4322_);
lean_dec_ref(v_e_4321_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* v_e_4328_, lean_object* v_xs_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = lean_expr_abstract(v_e_4328_, v_xs_4329_);
lean_dec_ref(v_xs_4329_);
lean_dec_ref(v_e_4328_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* v_e_4334_, lean_object* v_n_4335_, lean_object* v_xs_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = lean_expr_abstract_range(v_e_4334_, v_n_4335_, v_xs_4336_);
lean_dec_ref(v_xs_4336_);
lean_dec(v_n_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* v_e_4338_, lean_object* v_fvar_4339_, lean_object* v_v_4340_){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4341_ = lean_unsigned_to_nat(1u);
v___x_4342_ = lean_mk_empty_array_with_capacity(v___x_4341_);
v___x_4343_ = lean_array_push(v___x_4342_, v_fvar_4339_);
v___x_4344_ = lean_expr_abstract(v_e_4338_, v___x_4343_);
lean_dec_ref(v___x_4343_);
v___x_4345_ = lean_expr_instantiate1(v___x_4344_, v_v_4340_);
lean_dec_ref(v___x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* v_e_4346_, lean_object* v_fvar_4347_, lean_object* v_v_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Expr_replaceFVar(v_e_4346_, v_fvar_4347_, v_v_4348_);
lean_dec_ref(v_v_4348_);
lean_dec_ref(v_e_4346_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* v_e_4350_, lean_object* v_fvarId_4351_, lean_object* v_v_4352_){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4353_ = l_Lean_Expr_fvar___override(v_fvarId_4351_);
v___x_4354_ = l_Lean_Expr_replaceFVar(v_e_4350_, v___x_4353_, v_v_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* v_e_4355_, lean_object* v_fvarId_4356_, lean_object* v_v_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_Expr_replaceFVarId(v_e_4355_, v_fvarId_4356_, v_v_4357_);
lean_dec_ref(v_v_4357_);
lean_dec_ref(v_e_4355_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* v_e_4359_, lean_object* v_fvars_4360_, lean_object* v_vs_4361_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_expr_abstract(v_e_4359_, v_fvars_4360_);
v___x_4363_ = lean_expr_instantiate_rev(v___x_4362_, v_vs_4361_);
lean_dec_ref(v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* v_e_4364_, lean_object* v_fvars_4365_, lean_object* v_vs_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_Expr_replaceFVars(v_e_4364_, v_fvars_4365_, v_vs_4366_);
lean_dec_ref(v_vs_4366_);
lean_dec_ref(v_fvars_4365_);
lean_dec_ref(v_e_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* v_x_4370_){
_start:
{
switch(lean_obj_tag(v_x_4370_))
{
case 4:
{
uint8_t v___x_4371_; 
v___x_4371_ = 1;
return v___x_4371_;
}
case 3:
{
uint8_t v___x_4372_; 
v___x_4372_ = 1;
return v___x_4372_;
}
case 0:
{
uint8_t v___x_4373_; 
v___x_4373_ = 1;
return v___x_4373_;
}
case 9:
{
uint8_t v___x_4374_; 
v___x_4374_ = 1;
return v___x_4374_;
}
case 2:
{
uint8_t v___x_4375_; 
v___x_4375_ = 1;
return v___x_4375_;
}
case 1:
{
uint8_t v___x_4376_; 
v___x_4376_ = 1;
return v___x_4376_;
}
default: 
{
uint8_t v___x_4377_; 
v___x_4377_ = 0;
return v___x_4377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* v_x_4378_){
_start:
{
uint8_t v_res_4379_; lean_object* v_r_4380_; 
v_res_4379_ = l_Lean_Expr_isAtomic(v_x_4378_);
lean_dec_ref(v_x_4378_);
v_r_4380_ = lean_box(v_res_4379_);
return v_r_4380_;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4386_ = lean_box(0);
v___x_4387_ = ((lean_object*)(l_Lean_mkDecIsTrue___closed__2));
v___x_4388_ = l_Lean_Expr_const___override(v___x_4387_, v___x_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* v_pred_4389_, lean_object* v_proof_4390_){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = lean_obj_once(&l_Lean_mkDecIsTrue___closed__3, &l_Lean_mkDecIsTrue___closed__3_once, _init_l_Lean_mkDecIsTrue___closed__3);
v___x_4392_ = l_Lean_mkAppB(v___x_4391_, v_pred_4389_, v_proof_4390_);
return v___x_4392_;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2(void){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4397_ = lean_box(0);
v___x_4398_ = ((lean_object*)(l_Lean_mkDecIsFalse___closed__1));
v___x_4399_ = l_Lean_Expr_const___override(v___x_4398_, v___x_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* v_pred_4400_, lean_object* v_proof_4401_){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = lean_obj_once(&l_Lean_mkDecIsFalse___closed__2, &l_Lean_mkDecIsFalse___closed__2_once, _init_l_Lean_mkDecIsFalse___closed__2);
v___x_4403_ = l_Lean_mkAppB(v___x_4402_, v_pred_4400_, v_proof_4401_);
return v___x_4403_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq_default(void){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_obj_once(&l_Lean_instInhabitedExpr___closed__2, &l_Lean_instInhabitedExpr___closed__2_once, _init_l_Lean_instInhabitedExpr___closed__2);
return v___x_4404_;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq(void){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Lean_instInhabitedExprStructEq_default;
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0(lean_object* v_val_4406_){
_start:
{
lean_inc_ref(v_val_4406_);
return v_val_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___lam__0___boxed(lean_object* v_val_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_instCoeExprExprStructEq___lam__0(v_val_4407_);
lean_dec_ref(v_val_4407_);
return v_res_4408_;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* v_x_4411_, lean_object* v_x_4412_){
_start:
{
uint8_t v___x_4413_; 
v___x_4413_ = lean_expr_equal(v_x_4411_, v_x_4412_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* v_x_4414_, lean_object* v_x_4415_){
_start:
{
uint8_t v_res_4416_; lean_object* v_r_4417_; 
v_res_4416_ = l_Lean_ExprStructEq_beq(v_x_4414_, v_x_4415_);
lean_dec_ref(v_x_4415_);
lean_dec_ref(v_x_4414_);
v_r_4417_ = lean_box(v_res_4416_);
return v_r_4417_;
}
}
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* v_x_4418_){
_start:
{
uint64_t v___x_4419_; 
v___x_4419_ = l_Lean_Expr_hash(v_x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* v_x_4420_){
_start:
{
uint64_t v_res_4421_; lean_object* v_r_4422_; 
v_res_4421_ = l_Lean_ExprStructEq_hash(v_x_4420_);
lean_dec_ref(v_x_4420_);
v_r_4422_ = lean_box_uint64(v_res_4421_);
return v_r_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* v_revArgs_4429_, lean_object* v_start_4430_, lean_object* v_b_4431_, lean_object* v_i_4432_){
_start:
{
uint8_t v___x_4433_; 
v___x_4433_ = lean_nat_dec_le(v_i_4432_, v_start_4430_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v_i_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4434_ = l_Lean_instInhabitedExpr;
v___x_4435_ = lean_unsigned_to_nat(1u);
v_i_4436_ = lean_nat_sub(v_i_4432_, v___x_4435_);
lean_dec(v_i_4432_);
v___x_4437_ = lean_array_get_borrowed(v___x_4434_, v_revArgs_4429_, v_i_4436_);
lean_inc(v___x_4437_);
v___x_4438_ = l_Lean_Expr_app___override(v_b_4431_, v___x_4437_);
v_b_4431_ = v___x_4438_;
v_i_4432_ = v_i_4436_;
goto _start;
}
else
{
lean_dec(v_i_4432_);
return v_b_4431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* v_revArgs_4440_, lean_object* v_start_4441_, lean_object* v_b_4442_, lean_object* v_i_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4440_, v_start_4441_, v_b_4442_, v_i_4443_);
lean_dec(v_start_4441_);
lean_dec_ref(v_revArgs_4440_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* v_f_4445_, lean_object* v_beginIdx_4446_, lean_object* v_endIdx_4447_, lean_object* v_revArgs_4448_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4448_, v_beginIdx_4446_, v_f_4445_, v_endIdx_4447_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* v_f_4450_, lean_object* v_beginIdx_4451_, lean_object* v_endIdx_4452_, lean_object* v_revArgs_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Expr_mkAppRevRange(v_f_4450_, v_beginIdx_4451_, v_endIdx_4452_, v_revArgs_4453_);
lean_dec_ref(v_revArgs_4453_);
lean_dec(v_beginIdx_4451_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go(lean_object* v_revArgs_4455_, uint8_t v_useZeta_4456_, uint8_t v_preserveMData_4457_, lean_object* v_sz_4458_, lean_object* v_e_4459_, lean_object* v_i_4460_){
_start:
{
switch(lean_obj_tag(v_e_4459_))
{
case 6:
{
lean_object* v_body_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; 
v_body_4466_ = lean_ctor_get(v_e_4459_, 2);
lean_inc_ref(v_body_4466_);
lean_dec_ref_known(v_e_4459_, 3);
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_add(v_i_4460_, v___x_4467_);
lean_dec(v_i_4460_);
v___x_4469_ = lean_nat_dec_lt(v___x_4468_, v_sz_4458_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; 
lean_dec(v___x_4468_);
v___x_4470_ = lean_expr_instantiate(v_body_4466_, v_revArgs_4455_);
lean_dec_ref(v_body_4466_);
return v___x_4470_;
}
else
{
v_e_4459_ = v_body_4466_;
v_i_4460_ = v___x_4468_;
goto _start;
}
}
case 8:
{
if (v_useZeta_4456_ == 0)
{
goto v___jp_4461_;
}
else
{
lean_object* v_value_4472_; lean_object* v_body_4473_; uint8_t v___x_4474_; 
v_value_4472_ = lean_ctor_get(v_e_4459_, 2);
v_body_4473_ = lean_ctor_get(v_e_4459_, 3);
v___x_4474_ = lean_nat_dec_lt(v_i_4460_, v_sz_4458_);
if (v___x_4474_ == 0)
{
goto v___jp_4461_;
}
else
{
lean_object* v___x_4475_; 
lean_inc_ref(v_body_4473_);
lean_inc_ref(v_value_4472_);
lean_dec_ref_known(v_e_4459_, 4);
v___x_4475_ = lean_expr_instantiate1(v_body_4473_, v_value_4472_);
lean_dec_ref(v_value_4472_);
lean_dec_ref(v_body_4473_);
v_e_4459_ = v___x_4475_;
goto _start;
}
}
}
case 10:
{
if (v_preserveMData_4457_ == 0)
{
lean_object* v_expr_4477_; 
v_expr_4477_ = lean_ctor_get(v_e_4459_, 1);
lean_inc_ref(v_expr_4477_);
lean_dec_ref_known(v_e_4459_, 2);
v_e_4459_ = v_expr_4477_;
goto _start;
}
else
{
goto v___jp_4461_;
}
}
default: 
{
goto v___jp_4461_;
}
}
v___jp_4461_:
{
lean_object* v_n_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_n_4462_ = lean_nat_sub(v_sz_4458_, v_i_4460_);
lean_dec(v_i_4460_);
v___x_4463_ = lean_expr_instantiate_range(v_e_4459_, v_n_4462_, v_sz_4458_, v_revArgs_4455_);
lean_dec_ref(v_e_4459_);
v___x_4464_ = lean_unsigned_to_nat(0u);
v___x_4465_ = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(v_revArgs_4455_, v___x_4464_, v___x_4463_, v_n_4462_);
return v___x_4465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRev_go___boxed(lean_object* v_revArgs_4479_, lean_object* v_useZeta_4480_, lean_object* v_preserveMData_4481_, lean_object* v_sz_4482_, lean_object* v_e_4483_, lean_object* v_i_4484_){
_start:
{
uint8_t v_useZeta_boxed_4485_; uint8_t v_preserveMData_boxed_4486_; lean_object* v_res_4487_; 
v_useZeta_boxed_4485_ = lean_unbox(v_useZeta_4480_);
v_preserveMData_boxed_4486_ = lean_unbox(v_preserveMData_4481_);
v_res_4487_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4479_, v_useZeta_boxed_4485_, v_preserveMData_boxed_4486_, v_sz_4482_, v_e_4483_, v_i_4484_);
lean_dec(v_sz_4482_);
lean_dec_ref(v_revArgs_4479_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* v_f_4488_, lean_object* v_revArgs_4489_, uint8_t v_useZeta_4490_, uint8_t v_preserveMData_4491_){
_start:
{
lean_object* v_sz_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v_sz_4492_ = lean_array_get_size(v_revArgs_4489_);
v___x_4493_ = lean_unsigned_to_nat(0u);
v___x_4494_ = lean_nat_dec_eq(v_sz_4492_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; 
v___x_4495_ = l___private_Lean_Expr_0__Lean_Expr_betaRev_go(v_revArgs_4489_, v_useZeta_4490_, v_preserveMData_4491_, v_sz_4492_, v_f_4488_, v___x_4493_);
return v___x_4495_;
}
else
{
return v_f_4488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* v_f_4496_, lean_object* v_revArgs_4497_, lean_object* v_useZeta_4498_, lean_object* v_preserveMData_4499_){
_start:
{
uint8_t v_useZeta_boxed_4500_; uint8_t v_preserveMData_boxed_4501_; lean_object* v_res_4502_; 
v_useZeta_boxed_4500_ = lean_unbox(v_useZeta_4498_);
v_preserveMData_boxed_4501_ = lean_unbox(v_preserveMData_4499_);
v_res_4502_ = l_Lean_Expr_betaRev(v_f_4496_, v_revArgs_4497_, v_useZeta_boxed_4500_, v_preserveMData_boxed_4501_);
lean_dec_ref(v_revArgs_4497_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* v_f_4503_, lean_object* v_args_4504_){
_start:
{
lean_object* v___x_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = l_Array_reverse___redArg(v_args_4504_);
v___x_4506_ = 0;
v___x_4507_ = l_Lean_Expr_betaRev(v_f_4503_, v___x_4505_, v___x_4506_, v___x_4506_);
lean_dec_ref(v___x_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object* v_x_4508_){
_start:
{
switch(lean_obj_tag(v_x_4508_))
{
case 6:
{
lean_object* v_body_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_body_4509_ = lean_ctor_get(v_x_4508_, 2);
v___x_4510_ = l_Lean_Expr_getNumHeadLambdas(v_body_4509_);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_nat_add(v___x_4510_, v___x_4511_);
lean_dec(v___x_4510_);
return v___x_4512_;
}
case 10:
{
lean_object* v_expr_4513_; 
v_expr_4513_ = lean_ctor_get(v_x_4508_, 1);
v_x_4508_ = v_expr_4513_;
goto _start;
}
default: 
{
lean_object* v___x_4515_; 
v___x_4515_ = lean_unsigned_to_nat(0u);
return v___x_4515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getNumHeadLambdas___boxed(lean_object* v_x_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Expr_getNumHeadLambdas(v_x_4516_);
lean_dec_ref(v_x_4516_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody(lean_object* v_x_4518_){
_start:
{
switch(lean_obj_tag(v_x_4518_))
{
case 6:
{
lean_object* v_body_4519_; 
v_body_4519_ = lean_ctor_get(v_x_4518_, 2);
v_x_4518_ = v_body_4519_;
goto _start;
}
case 10:
{
lean_object* v_expr_4521_; 
v_expr_4521_ = lean_ctor_get(v_x_4518_, 1);
v_x_4518_ = v_expr_4521_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_4518_);
return v_x_4518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getLambdaBody___boxed(lean_object* v_x_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Expr_getLambdaBody(v_x_4523_);
lean_dec_ref(v_x_4523_);
return v_res_4524_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t v_useZeta_4525_, lean_object* v_x_4526_){
_start:
{
switch(lean_obj_tag(v_x_4526_))
{
case 6:
{
uint8_t v___x_4527_; 
v___x_4527_ = 1;
return v___x_4527_;
}
case 8:
{
if (v_useZeta_4525_ == 0)
{
return v_useZeta_4525_;
}
else
{
lean_object* v_body_4528_; 
v_body_4528_ = lean_ctor_get(v_x_4526_, 3);
v_x_4526_ = v_body_4528_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_4530_; 
v_expr_4530_ = lean_ctor_get(v_x_4526_, 1);
v_x_4526_ = v_expr_4530_;
goto _start;
}
default: 
{
uint8_t v___x_4532_; 
v___x_4532_ = 0;
return v___x_4532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* v_useZeta_4533_, lean_object* v_x_4534_){
_start:
{
uint8_t v_useZeta_boxed_4535_; uint8_t v_res_4536_; lean_object* v_r_4537_; 
v_useZeta_boxed_4535_ = lean_unbox(v_useZeta_4533_);
v_res_4536_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_boxed_4535_, v_x_4534_);
lean_dec_ref(v_x_4534_);
v_r_4537_ = lean_box(v_res_4536_);
return v_r_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* v_e_4538_){
_start:
{
lean_object* v_f_4539_; uint8_t v___x_4540_; uint8_t v___x_4541_; 
v_f_4539_ = l_Lean_Expr_getAppFn(v_e_4538_);
v___x_4540_ = 0;
v___x_4541_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_4540_, v_f_4539_);
if (v___x_4541_ == 0)
{
lean_dec_ref(v_f_4539_);
return v_e_4538_;
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4542_ = l_Lean_Expr_getAppNumArgs(v_e_4538_);
v___x_4543_ = lean_mk_empty_array_with_capacity(v___x_4542_);
lean_dec(v___x_4542_);
v___x_4544_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_4538_, v___x_4543_);
v___x_4545_ = l_Lean_Expr_betaRev(v_f_4539_, v___x_4544_, v___x_4540_, v___x_4540_);
lean_dec_ref(v___x_4544_);
return v___x_4545_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* v_e_4546_, uint8_t v_useZeta_4547_){
_start:
{
uint8_t v___x_4548_; 
v___x_4548_ = l_Lean_Expr_isApp(v_e_4546_);
if (v___x_4548_ == 0)
{
return v___x_4548_;
}
else
{
lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4549_ = l_Lean_Expr_getAppFn(v_e_4546_);
v___x_4550_ = l_Lean_Expr_isHeadBetaTargetFn(v_useZeta_4547_, v___x_4549_);
lean_dec_ref(v___x_4549_);
return v___x_4550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* v_e_4551_, lean_object* v_useZeta_4552_){
_start:
{
uint8_t v_useZeta_boxed_4553_; uint8_t v_res_4554_; lean_object* v_r_4555_; 
v_useZeta_boxed_4553_ = lean_unbox(v_useZeta_4552_);
v_res_4554_ = l_Lean_Expr_isHeadBetaTarget(v_e_4551_, v_useZeta_boxed_4553_);
lean_dec_ref(v_e_4551_);
v_r_4555_ = lean_box(v_res_4554_);
return v_r_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* v_x_4556_, lean_object* v_x_4557_, lean_object* v_x_4558_){
_start:
{
lean_object* v_f_4560_; 
if (lean_obj_tag(v_x_4556_) == 5)
{
lean_object* v_arg_4564_; 
v_arg_4564_ = lean_ctor_get(v_x_4556_, 1);
if (lean_obj_tag(v_arg_4564_) == 0)
{
lean_object* v_fn_4565_; lean_object* v_deBruijnIndex_4566_; lean_object* v_zero_4567_; uint8_t v_isZero_4568_; 
v_fn_4565_ = lean_ctor_get(v_x_4556_, 0);
v_deBruijnIndex_4566_ = lean_ctor_get(v_arg_4564_, 0);
v_zero_4567_ = lean_unsigned_to_nat(0u);
v_isZero_4568_ = lean_nat_dec_eq(v_x_4557_, v_zero_4567_);
if (v_isZero_4568_ == 1)
{
lean_dec(v_x_4558_);
lean_dec(v_x_4557_);
v_f_4560_ = v_x_4556_;
goto v___jp_4559_;
}
else
{
uint8_t v___x_4569_; 
lean_inc(v_deBruijnIndex_4566_);
lean_inc_ref(v_fn_4565_);
lean_dec_ref_known(v_x_4556_, 2);
v___x_4569_ = lean_nat_dec_eq(v_deBruijnIndex_4566_, v_x_4558_);
lean_dec(v_deBruijnIndex_4566_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; 
lean_dec_ref(v_fn_4565_);
lean_dec(v_x_4558_);
lean_dec(v_x_4557_);
v___x_4570_ = lean_box(0);
return v___x_4570_;
}
else
{
lean_object* v_one_4571_; lean_object* v_n_4572_; lean_object* v___x_4573_; 
v_one_4571_ = lean_unsigned_to_nat(1u);
v_n_4572_ = lean_nat_sub(v_x_4557_, v_one_4571_);
lean_dec(v_x_4557_);
v___x_4573_ = lean_nat_add(v_x_4558_, v_one_4571_);
lean_dec(v_x_4558_);
v_x_4556_ = v_fn_4565_;
v_x_4557_ = v_n_4572_;
v_x_4558_ = v___x_4573_;
goto _start;
}
}
}
else
{
lean_object* v_zero_4575_; uint8_t v_isZero_4576_; 
lean_dec(v_x_4558_);
v_zero_4575_ = lean_unsigned_to_nat(0u);
v_isZero_4576_ = lean_nat_dec_eq(v_x_4557_, v_zero_4575_);
lean_dec(v_x_4557_);
if (v_isZero_4576_ == 1)
{
v_f_4560_ = v_x_4556_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4577_; 
lean_dec_ref_known(v_x_4556_, 2);
v___x_4577_ = lean_box(0);
return v___x_4577_;
}
}
}
else
{
lean_object* v_zero_4578_; uint8_t v_isZero_4579_; 
lean_dec(v_x_4558_);
v_zero_4578_ = lean_unsigned_to_nat(0u);
v_isZero_4579_ = lean_nat_dec_eq(v_x_4557_, v_zero_4578_);
lean_dec(v_x_4557_);
if (v_isZero_4579_ == 1)
{
v_f_4560_ = v_x_4556_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4580_; 
lean_dec_ref(v_x_4556_);
v___x_4580_ = lean_box(0);
return v___x_4580_;
}
}
v___jp_4559_:
{
uint8_t v___x_4561_; 
v___x_4561_ = l_Lean_Expr_hasLooseBVars(v_f_4560_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_f_4560_);
return v___x_4562_;
}
else
{
lean_object* v___x_4563_; 
lean_dec_ref(v_f_4560_);
v___x_4563_ = lean_box(0);
return v___x_4563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
if (lean_obj_tag(v_x_4581_) == 6)
{
lean_object* v_body_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v_body_4583_ = lean_ctor_get(v_x_4581_, 2);
lean_inc_ref(v_body_4583_);
lean_dec_ref_known(v_x_4581_, 3);
v___x_4584_ = lean_unsigned_to_nat(1u);
v___x_4585_ = lean_nat_add(v_x_4582_, v___x_4584_);
lean_dec(v_x_4582_);
v_x_4581_ = v_body_4583_;
v_x_4582_ = v___x_4585_;
goto _start;
}
else
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4587_ = lean_unsigned_to_nat(0u);
v___x_4588_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(v_x_4581_, v_x_4582_, v___x_4587_);
return v___x_4588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* v_e_4589_){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4590_ = lean_unsigned_to_nat(0u);
v___x_4591_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_e_4589_, v___x_4590_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* v_x_4592_){
_start:
{
if (lean_obj_tag(v_x_4592_) == 6)
{
lean_object* v_body_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v_body_4593_ = lean_ctor_get(v_x_4592_, 2);
lean_inc_ref(v_body_4593_);
lean_dec_ref_known(v_x_4592_, 3);
v___x_4594_ = lean_unsigned_to_nat(1u);
v___x_4595_ = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(v_body_4593_, v___x_4594_);
return v___x_4595_;
}
else
{
lean_object* v___x_4596_; 
lean_dec_ref(v_x_4592_);
v___x_4596_ = lean_box(0);
return v___x_4596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* v_e_4600_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4601_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4602_ = lean_unsigned_to_nat(2u);
v___x_4603_ = l_Lean_Expr_isAppOfArity(v_e_4600_, v___x_4601_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
v___x_4604_ = lean_box(0);
return v___x_4604_;
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = l_Lean_Expr_appArg_x21(v_e_4600_);
v___x_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
return v___x_4606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* v_e_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_Lean_Expr_getOptParamDefault_x3f(v_e_4607_);
lean_dec_ref(v_e_4607_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* v_e_4612_){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; 
v___x_4613_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4614_ = lean_unsigned_to_nat(2u);
v___x_4615_ = l_Lean_Expr_isAppOfArity(v_e_4612_, v___x_4613_, v___x_4614_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_box(0);
return v___x_4616_;
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = l_Lean_Expr_appArg_x21(v_e_4612_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* v_e_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_Expr_getAutoParamTactic_x3f(v_e_4619_);
lean_dec_ref(v_e_4619_);
return v_res_4620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOutParam(lean_object* v_e_4624_){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4625_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4626_ = lean_unsigned_to_nat(1u);
v___x_4627_ = l_Lean_Expr_isAppOfArity(v_e_4624_, v___x_4625_, v___x_4626_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* v_e_4628_){
_start:
{
uint8_t v_res_4629_; lean_object* v_r_4630_; 
v_res_4629_ = l_Lean_Expr_isOutParam(v_e_4628_);
lean_dec_ref(v_e_4628_);
v_r_4630_ = lean_box(v_res_4629_);
return v_r_4630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSemiOutParam(lean_object* v_e_4634_){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4635_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4636_ = lean_unsigned_to_nat(1u);
v___x_4637_ = l_Lean_Expr_isAppOfArity(v_e_4634_, v___x_4635_, v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSemiOutParam___boxed(lean_object* v_e_4638_){
_start:
{
uint8_t v_res_4639_; lean_object* v_r_4640_; 
v_res_4639_ = l_Lean_Expr_isSemiOutParam(v_e_4638_);
lean_dec_ref(v_e_4638_);
v_r_4640_ = lean_box(v_res_4639_);
return v_r_4640_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* v_e_4641_){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4643_ = lean_unsigned_to_nat(2u);
v___x_4644_ = l_Lean_Expr_isAppOfArity(v_e_4641_, v___x_4642_, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* v_e_4645_){
_start:
{
uint8_t v_res_4646_; lean_object* v_r_4647_; 
v_res_4646_ = l_Lean_Expr_isOptParam(v_e_4645_);
lean_dec_ref(v_e_4645_);
v_r_4647_ = lean_box(v_res_4646_);
return v_r_4647_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* v_e_4648_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4649_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4650_ = lean_unsigned_to_nat(2u);
v___x_4651_ = l_Lean_Expr_isAppOfArity(v_e_4648_, v___x_4649_, v___x_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* v_e_4652_){
_start:
{
uint8_t v_res_4653_; lean_object* v_r_4654_; 
v_res_4653_ = l_Lean_Expr_isAutoParam(v_e_4652_);
lean_dec_ref(v_e_4652_);
v_r_4654_ = lean_box(v_res_4653_);
return v_r_4654_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTypeAnnotation(lean_object* v_e_4655_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_Expr_getAppFn(v_e_4655_);
if (lean_obj_tag(v___x_4656_) == 4)
{
lean_object* v_declName_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v_declName_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_declName_4657_);
lean_dec_ref_known(v___x_4656_, 2);
v___x_4658_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4659_ = lean_name_eq(v_declName_4657_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4660_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4661_ = lean_name_eq(v_declName_4657_, v___x_4660_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4662_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4663_ = lean_name_eq(v_declName_4657_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; uint8_t v___x_4665_; 
v___x_4664_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4665_ = lean_name_eq(v_declName_4657_, v___x_4664_);
lean_dec(v_declName_4657_);
return v___x_4665_;
}
else
{
lean_dec(v_declName_4657_);
return v___x_4663_;
}
}
else
{
lean_dec(v_declName_4657_);
return v___x_4661_;
}
}
else
{
lean_dec(v_declName_4657_);
return v___x_4659_;
}
}
else
{
uint8_t v___x_4666_; 
lean_dec_ref(v___x_4656_);
v___x_4666_ = 0;
return v___x_4666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTypeAnnotation___boxed(lean_object* v_e_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_Lean_Expr_isTypeAnnotation(v_e_4667_);
lean_dec_ref(v_e_4667_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* v_e_4670_){
_start:
{
if (lean_obj_tag(v_e_4670_) == 5)
{
lean_object* v_fn_4671_; 
v_fn_4671_ = lean_ctor_get(v_e_4670_, 0);
switch(lean_obj_tag(v_fn_4671_))
{
case 4:
{
lean_object* v_arg_4672_; lean_object* v_declName_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v_arg_4672_ = lean_ctor_get(v_e_4670_, 1);
v_declName_4673_ = lean_ctor_get(v_fn_4671_, 0);
v___x_4674_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4675_ = lean_name_eq(v_declName_4673_, v___x_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; uint8_t v___x_4677_; 
v___x_4676_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4677_ = lean_name_eq(v_declName_4673_, v___x_4676_);
if (v___x_4677_ == 0)
{
return v_e_4670_;
}
else
{
lean_inc_ref(v_arg_4672_);
lean_dec_ref_known(v_e_4670_, 2);
v_e_4670_ = v_arg_4672_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4672_);
lean_dec_ref_known(v_e_4670_, 2);
v_e_4670_ = v_arg_4672_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4680_; 
v_fn_4680_ = lean_ctor_get(v_fn_4671_, 0);
if (lean_obj_tag(v_fn_4680_) == 4)
{
lean_object* v_arg_4681_; lean_object* v_declName_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; 
v_arg_4681_ = lean_ctor_get(v_fn_4671_, 1);
v_declName_4682_ = lean_ctor_get(v_fn_4680_, 0);
v___x_4683_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4684_ = lean_name_eq(v_declName_4682_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4685_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4686_ = lean_name_eq(v_declName_4682_, v___x_4685_);
if (v___x_4686_ == 0)
{
return v_e_4670_;
}
else
{
lean_inc_ref(v_arg_4681_);
lean_dec_ref_known(v_e_4670_, 2);
v_e_4670_ = v_arg_4681_;
goto _start;
}
}
else
{
lean_inc_ref(v_arg_4681_);
lean_dec_ref_known(v_e_4670_, 2);
v_e_4670_ = v_arg_4681_;
goto _start;
}
}
else
{
return v_e_4670_;
}
}
default: 
{
return v_e_4670_;
}
}
}
else
{
return v_e_4670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* v_e_4689_){
_start:
{
switch(lean_obj_tag(v_e_4689_))
{
case 10:
{
lean_object* v_expr_4690_; 
v_expr_4690_ = lean_ctor_get(v_e_4689_, 1);
v_e_4689_ = v_expr_4690_;
goto _start;
}
case 5:
{
lean_object* v_fn_4692_; 
v_fn_4692_ = lean_ctor_get(v_e_4689_, 0);
switch(lean_obj_tag(v_fn_4692_))
{
case 4:
{
lean_object* v_arg_4693_; lean_object* v_declName_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_arg_4693_ = lean_ctor_get(v_e_4689_, 1);
v_declName_4694_ = lean_ctor_get(v_fn_4692_, 0);
v___x_4695_ = ((lean_object*)(l_Lean_Expr_isOutParam___closed__1));
v___x_4696_ = lean_name_eq(v_declName_4694_, v___x_4695_);
if (v___x_4696_ == 0)
{
lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Expr_isSemiOutParam___closed__1));
v___x_4698_ = lean_name_eq(v_declName_4694_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_inc_ref(v_e_4689_);
return v_e_4689_;
}
else
{
v_e_4689_ = v_arg_4693_;
goto _start;
}
}
else
{
v_e_4689_ = v_arg_4693_;
goto _start;
}
}
case 5:
{
lean_object* v_fn_4701_; 
v_fn_4701_ = lean_ctor_get(v_fn_4692_, 0);
if (lean_obj_tag(v_fn_4701_) == 4)
{
lean_object* v_arg_4702_; lean_object* v_declName_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; 
v_arg_4702_ = lean_ctor_get(v_fn_4692_, 1);
v_declName_4703_ = lean_ctor_get(v_fn_4701_, 0);
v___x_4704_ = ((lean_object*)(l_Lean_Expr_getOptParamDefault_x3f___closed__1));
v___x_4705_ = lean_name_eq(v_declName_4703_, v___x_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_Expr_getAutoParamTactic_x3f___closed__1));
v___x_4707_ = lean_name_eq(v_declName_4703_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_inc_ref(v_e_4689_);
return v_e_4689_;
}
else
{
v_e_4689_ = v_arg_4702_;
goto _start;
}
}
else
{
v_e_4689_ = v_arg_4702_;
goto _start;
}
}
else
{
lean_inc_ref(v_e_4689_);
return v_e_4689_;
}
}
default: 
{
lean_inc_ref(v_e_4689_);
return v_e_4689_;
}
}
}
default: 
{
lean_inc_ref(v_e_4689_);
return v_e_4689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations___boxed(lean_object* v_e_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Lean_Expr_cleanupAnnotations(v_e_4710_);
lean_dec_ref(v_e_4710_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object* v_e_4712_){
_start:
{
lean_object* v_fn_4713_; lean_object* v___x_4714_; 
v_fn_4713_ = lean_ctor_get(v_e_4712_, 0);
v___x_4714_ = l_Lean_Expr_cleanupAnnotations(v_fn_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___redArg___boxed(lean_object* v_e_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4715_);
lean_dec_ref(v_e_4715_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup(lean_object* v_e_4717_, lean_object* v_h_4718_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Expr_appFnCleanup___redArg(v_e_4717_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFnCleanup___boxed(lean_object* v_e_4720_, lean_object* v_h_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Lean_Expr_appFnCleanup(v_e_4720_, v_h_4721_);
lean_dec_ref(v_e_4720_);
return v_res_4722_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFalse(lean_object* v_e_4726_){
_start:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4727_ = l_Lean_Expr_cleanupAnnotations(v_e_4726_);
v___x_4728_ = ((lean_object*)(l_Lean_Expr_isFalse___closed__1));
v___x_4729_ = l_Lean_Expr_isConstOf(v___x_4727_, v___x_4728_);
lean_dec_ref(v___x_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isFalse___boxed(lean_object* v_e_4730_){
_start:
{
uint8_t v_res_4731_; lean_object* v_r_4732_; 
v_res_4731_ = l_Lean_Expr_isFalse(v_e_4730_);
lean_dec_ref(v_e_4730_);
v_r_4732_ = lean_box(v_res_4731_);
return v_r_4732_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isTrue(lean_object* v_e_4736_){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4737_ = l_Lean_Expr_cleanupAnnotations(v_e_4736_);
v___x_4738_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_4739_ = l_Lean_Expr_isConstOf(v___x_4737_, v___x_4738_);
lean_dec_ref(v___x_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isTrue___boxed(lean_object* v_e_4740_){
_start:
{
uint8_t v_res_4741_; lean_object* v_r_4742_; 
v_res_4741_ = l_Lean_Expr_isTrue(v_e_4740_);
lean_dec_ref(v_e_4740_);
v_r_4742_ = lean_box(v_res_4741_);
return v_r_4742_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolFalse(lean_object* v_e_4748_){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4749_ = l_Lean_Expr_cleanupAnnotations(v_e_4748_);
v___x_4750_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
v___x_4751_ = l_Lean_Expr_isConstOf(v___x_4749_, v___x_4750_);
lean_dec_ref(v___x_4749_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolFalse___boxed(lean_object* v_e_4752_){
_start:
{
uint8_t v_res_4753_; lean_object* v_r_4754_; 
v_res_4753_ = l_Lean_Expr_isBoolFalse(v_e_4752_);
lean_dec_ref(v_e_4752_);
v_r_4754_ = lean_box(v_res_4753_);
return v_r_4754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBoolTrue(lean_object* v_e_4758_){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___x_4759_ = l_Lean_Expr_cleanupAnnotations(v_e_4758_);
v___x_4760_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_4761_ = l_Lean_Expr_isConstOf(v___x_4759_, v___x_4760_);
lean_dec_ref(v___x_4759_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isBoolTrue___boxed(lean_object* v_e_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l_Lean_Expr_isBoolTrue(v_e_4762_);
lean_dec_ref(v_e_4762_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallArity(lean_object* v_x_4765_){
_start:
{
switch(lean_obj_tag(v_x_4765_))
{
case 10:
{
lean_object* v_expr_4766_; 
v_expr_4766_ = lean_ctor_get(v_x_4765_, 1);
lean_inc_ref(v_expr_4766_);
lean_dec_ref_known(v_x_4765_, 2);
v_x_4765_ = v_expr_4766_;
goto _start;
}
case 7:
{
lean_object* v_body_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_body_4768_ = lean_ctor_get(v_x_4765_, 2);
lean_inc_ref(v_body_4768_);
lean_dec_ref_known(v_x_4765_, 3);
v___x_4769_ = l_Lean_Expr_getForallArity(v_body_4768_);
v___x_4770_ = lean_unsigned_to_nat(1u);
v___x_4771_ = lean_nat_add(v___x_4769_, v___x_4770_);
lean_dec(v___x_4769_);
return v___x_4771_;
}
default: 
{
uint8_t v___x_4772_; uint8_t v___x_4773_; 
v___x_4772_ = 0;
v___x_4773_ = l_Lean_Expr_isHeadBetaTarget(v_x_4765_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v_e_x27_4774_; uint8_t v___x_4775_; 
v_e_x27_4774_ = l_Lean_Expr_cleanupAnnotations(v_x_4765_);
v___x_4775_ = lean_expr_eqv(v_x_4765_, v_e_x27_4774_);
lean_dec_ref(v_x_4765_);
if (v___x_4775_ == 0)
{
v_x_4765_ = v_e_x27_4774_;
goto _start;
}
else
{
lean_object* v___x_4777_; 
lean_dec_ref(v_e_x27_4774_);
v___x_4777_ = lean_unsigned_to_nat(0u);
return v___x_4777_;
}
}
else
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_Expr_headBeta(v_x_4765_);
v_x_4765_ = v___x_4778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f(lean_object* v_e_4780_){
_start:
{
lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4781_ = l_Lean_Expr_cleanupAnnotations(v_e_4780_);
v___x_4782_ = l_Lean_Expr_isApp(v___x_4781_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
lean_dec_ref(v___x_4781_);
v___x_4783_ = lean_box(0);
return v___x_4783_;
}
else
{
lean_object* v___x_4784_; uint8_t v___x_4785_; 
v___x_4784_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4781_);
lean_dec_ref(v___x_4781_);
v___x_4785_ = l_Lean_Expr_isApp(v___x_4784_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; 
lean_dec_ref(v___x_4784_);
v___x_4786_ = lean_box(0);
return v___x_4786_;
}
else
{
lean_object* v_arg_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v_arg_4787_ = lean_ctor_get(v___x_4784_, 1);
lean_inc_ref(v_arg_4787_);
v___x_4788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4784_);
lean_dec_ref(v___x_4784_);
v___x_4789_ = l_Lean_Expr_isApp(v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref(v___x_4788_);
lean_dec_ref(v_arg_4787_);
v___x_4790_ = lean_box(0);
return v___x_4790_;
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4791_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4788_);
lean_dec_ref(v___x_4788_);
v___x_4792_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__2));
v___x_4793_ = l_Lean_Expr_isConstOf(v___x_4791_, v___x_4792_);
lean_dec_ref(v___x_4791_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; 
lean_dec_ref(v_arg_4787_);
v___x_4794_ = lean_box(0);
return v___x_4794_;
}
else
{
if (lean_obj_tag(v_arg_4787_) == 9)
{
lean_object* v_a_4795_; 
v_a_4795_ = lean_ctor_get(v_arg_4787_, 0);
lean_inc_ref(v_a_4795_);
lean_dec_ref_known(v_arg_4787_, 1);
if (lean_obj_tag(v_a_4795_) == 0)
{
lean_object* v_val_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
v_val_4796_ = lean_ctor_get(v_a_4795_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_a_4795_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v_a_4795_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_val_4796_);
lean_dec(v_a_4795_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
lean_ctor_set_tag(v___x_4798_, 1);
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_val_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
else
{
lean_object* v___x_4804_; 
lean_dec_ref(v_a_4795_);
v___x_4804_ = lean_box(0);
return v___x_4804_;
}
}
else
{
lean_object* v___x_4805_; 
lean_dec_ref(v_arg_4787_);
v___x_4805_ = lean_box(0);
return v___x_4805_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_nat_x3f___boxed(lean_object* v_e_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_Expr_nat_x3f(v_e_4806_);
lean_dec_ref(v_e_4806_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f(lean_object* v_e_4813_){
_start:
{
lean_object* v___x_4826_; uint8_t v___x_4827_; 
v___x_4826_ = l_Lean_Expr_cleanupAnnotations(v_e_4813_);
v___x_4827_ = l_Lean_Expr_isApp(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_dec_ref(v___x_4826_);
goto v___jp_4814_;
}
else
{
lean_object* v_arg_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_arg_4828_ = lean_ctor_get(v___x_4826_, 1);
lean_inc_ref(v_arg_4828_);
v___x_4829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4826_);
lean_dec_ref(v___x_4826_);
v___x_4830_ = l_Lean_Expr_isApp(v___x_4829_);
if (v___x_4830_ == 0)
{
lean_dec_ref(v___x_4829_);
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4829_);
lean_dec_ref(v___x_4829_);
v___x_4832_ = l_Lean_Expr_isApp(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec_ref(v___x_4831_);
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4831_);
lean_dec_ref(v___x_4831_);
v___x_4834_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_4835_ = l_Lean_Expr_isConstOf(v___x_4833_, v___x_4834_);
lean_dec_ref(v___x_4833_);
if (v___x_4835_ == 0)
{
lean_dec_ref(v_arg_4828_);
goto v___jp_4814_;
}
else
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_Expr_nat_x3f(v_arg_4828_);
lean_dec_ref(v_arg_4828_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_box(0);
return v___x_4837_;
}
else
{
lean_object* v_val_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4850_; 
v_val_4838_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4840_ = v___x_4836_;
v_isShared_4841_ = v_isSharedCheck_4850_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_val_4838_);
lean_dec(v___x_4836_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4850_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; uint8_t v___x_4843_; 
v___x_4842_ = lean_unsigned_to_nat(0u);
v___x_4843_ = lean_nat_dec_eq(v_val_4838_, v___x_4842_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4844_ = lean_nat_to_int(v_val_4838_);
v___x_4845_ = lean_int_neg(v___x_4844_);
lean_dec(v___x_4844_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v___x_4845_);
v___x_4847_ = v___x_4840_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
else
{
lean_object* v___x_4849_; 
lean_del_object(v___x_4840_);
lean_dec(v_val_4838_);
v___x_4849_ = lean_box(0);
return v___x_4849_;
}
}
}
}
}
}
}
v___jp_4814_:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Expr_nat_x3f(v_e_4813_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_box(0);
return v___x_4816_;
}
else
{
lean_object* v_val_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4825_; 
v_val_4817_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4819_ = v___x_4815_;
v_isShared_4820_ = v_isSharedCheck_4825_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_val_4817_);
lean_dec(v___x_4815_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4825_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4821_ = lean_nat_to_int(v_val_4817_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4821_);
v___x_4823_ = v___x_4819_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_int_x3f___boxed(lean_object* v_e_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Lean_Expr_int_x3f(v_e_4851_);
lean_dec_ref(v_e_4851_);
return v_res_4852_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(lean_object* v_p_4853_, lean_object* v_e_4854_){
_start:
{
uint8_t v___x_4855_; lean_object* v_d_4857_; lean_object* v_b_4858_; 
v___x_4855_ = l_Lean_Expr_hasFVar(v_e_4854_);
if (v___x_4855_ == 0)
{
lean_dec_ref(v_e_4854_);
lean_dec_ref(v_p_4853_);
return v___x_4855_;
}
else
{
switch(lean_obj_tag(v_e_4854_))
{
case 7:
{
lean_object* v_binderType_4861_; lean_object* v_body_4862_; 
v_binderType_4861_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_binderType_4861_);
v_body_4862_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_body_4862_);
lean_dec_ref_known(v_e_4854_, 3);
v_d_4857_ = v_binderType_4861_;
v_b_4858_ = v_body_4862_;
goto v___jp_4856_;
}
case 6:
{
lean_object* v_binderType_4863_; lean_object* v_body_4864_; 
v_binderType_4863_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_binderType_4863_);
v_body_4864_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_body_4864_);
lean_dec_ref_known(v_e_4854_, 3);
v_d_4857_ = v_binderType_4863_;
v_b_4858_ = v_body_4864_;
goto v___jp_4856_;
}
case 10:
{
lean_object* v_expr_4865_; 
v_expr_4865_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_expr_4865_);
lean_dec_ref_known(v_e_4854_, 2);
v_e_4854_ = v_expr_4865_;
goto _start;
}
case 8:
{
lean_object* v_type_4867_; lean_object* v_value_4868_; lean_object* v_body_4869_; uint8_t v___x_4870_; 
v_type_4867_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_type_4867_);
v_value_4868_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_value_4868_);
v_body_4869_ = lean_ctor_get(v_e_4854_, 3);
lean_inc_ref(v_body_4869_);
lean_dec_ref_known(v_e_4854_, 4);
lean_inc_ref(v_p_4853_);
v___x_4870_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_type_4867_);
if (v___x_4870_ == 0)
{
uint8_t v___x_4871_; 
lean_inc_ref(v_p_4853_);
v___x_4871_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_value_4868_);
if (v___x_4871_ == 0)
{
v_e_4854_ = v_body_4869_;
goto _start;
}
else
{
lean_dec_ref(v_body_4869_);
lean_dec_ref(v_p_4853_);
return v___x_4855_;
}
}
else
{
lean_dec_ref(v_body_4869_);
lean_dec_ref(v_value_4868_);
lean_dec_ref(v_p_4853_);
return v___x_4855_;
}
}
case 5:
{
lean_object* v_fn_4873_; lean_object* v_arg_4874_; uint8_t v___x_4875_; 
v_fn_4873_ = lean_ctor_get(v_e_4854_, 0);
lean_inc_ref(v_fn_4873_);
v_arg_4874_ = lean_ctor_get(v_e_4854_, 1);
lean_inc_ref(v_arg_4874_);
lean_dec_ref_known(v_e_4854_, 2);
lean_inc_ref(v_p_4853_);
v___x_4875_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_fn_4873_);
if (v___x_4875_ == 0)
{
v_e_4854_ = v_arg_4874_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4874_);
lean_dec_ref(v_p_4853_);
return v___x_4855_;
}
}
case 11:
{
lean_object* v_struct_4877_; 
v_struct_4877_ = lean_ctor_get(v_e_4854_, 2);
lean_inc_ref(v_struct_4877_);
lean_dec_ref_known(v_e_4854_, 3);
v_e_4854_ = v_struct_4877_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4879_; lean_object* v___x_4880_; uint8_t v___x_4881_; 
v_fvarId_4879_ = lean_ctor_get(v_e_4854_, 0);
lean_inc(v_fvarId_4879_);
lean_dec_ref_known(v_e_4854_, 1);
v___x_4880_ = lean_apply_1(v_p_4853_, v_fvarId_4879_);
v___x_4881_ = lean_unbox(v___x_4880_);
return v___x_4881_;
}
default: 
{
uint8_t v___x_4882_; 
lean_dec_ref(v_e_4854_);
lean_dec_ref(v_p_4853_);
v___x_4882_ = 0;
return v___x_4882_;
}
}
}
v___jp_4856_:
{
uint8_t v___x_4859_; 
lean_inc_ref(v_p_4853_);
v___x_4859_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4853_, v_d_4857_);
if (v___x_4859_ == 0)
{
v_e_4854_ = v_b_4858_;
goto _start;
}
else
{
lean_dec_ref(v_b_4858_);
lean_dec_ref(v_p_4853_);
return v___x_4855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___boxed(lean_object* v_p_4883_, lean_object* v_e_4884_){
_start:
{
uint8_t v_res_4885_; lean_object* v_r_4886_; 
v_res_4885_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4883_, v_e_4884_);
v_r_4886_ = lean_box(v_res_4885_);
return v_r_4886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar(lean_object* v_e_4887_, lean_object* v_p_4888_){
_start:
{
uint8_t v___x_4889_; 
v___x_4889_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit(v_p_4888_, v_e_4887_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar___boxed(lean_object* v_e_4890_, lean_object* v_p_4891_){
_start:
{
uint8_t v_res_4892_; lean_object* v_r_4893_; 
v_res_4892_ = l_Lean_Expr_hasAnyFVar(v_e_4890_, v_p_4891_);
v_r_4893_ = lean_box(v_res_4892_);
return v_r_4893_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(lean_object* v_fvarId_4894_, lean_object* v_e_4895_){
_start:
{
uint8_t v___x_4896_; lean_object* v_d_4898_; lean_object* v_b_4899_; 
v___x_4896_ = l_Lean_Expr_hasFVar(v_e_4895_);
if (v___x_4896_ == 0)
{
return v___x_4896_;
}
else
{
switch(lean_obj_tag(v_e_4895_))
{
case 7:
{
lean_object* v_binderType_4902_; lean_object* v_body_4903_; 
v_binderType_4902_ = lean_ctor_get(v_e_4895_, 1);
v_body_4903_ = lean_ctor_get(v_e_4895_, 2);
v_d_4898_ = v_binderType_4902_;
v_b_4899_ = v_body_4903_;
goto v___jp_4897_;
}
case 6:
{
lean_object* v_binderType_4904_; lean_object* v_body_4905_; 
v_binderType_4904_ = lean_ctor_get(v_e_4895_, 1);
v_body_4905_ = lean_ctor_get(v_e_4895_, 2);
v_d_4898_ = v_binderType_4904_;
v_b_4899_ = v_body_4905_;
goto v___jp_4897_;
}
case 10:
{
lean_object* v_expr_4906_; 
v_expr_4906_ = lean_ctor_get(v_e_4895_, 1);
v_e_4895_ = v_expr_4906_;
goto _start;
}
case 8:
{
lean_object* v_type_4908_; lean_object* v_value_4909_; lean_object* v_body_4910_; uint8_t v___x_4911_; 
v_type_4908_ = lean_ctor_get(v_e_4895_, 1);
v_value_4909_ = lean_ctor_get(v_e_4895_, 2);
v_body_4910_ = lean_ctor_get(v_e_4895_, 3);
v___x_4911_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4894_, v_type_4908_);
if (v___x_4911_ == 0)
{
uint8_t v___x_4912_; 
v___x_4912_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4894_, v_value_4909_);
if (v___x_4912_ == 0)
{
v_e_4895_ = v_body_4910_;
goto _start;
}
else
{
return v___x_4896_;
}
}
else
{
return v___x_4896_;
}
}
case 5:
{
lean_object* v_fn_4914_; lean_object* v_arg_4915_; uint8_t v___x_4916_; 
v_fn_4914_ = lean_ctor_get(v_e_4895_, 0);
v_arg_4915_ = lean_ctor_get(v_e_4895_, 1);
v___x_4916_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4894_, v_fn_4914_);
if (v___x_4916_ == 0)
{
v_e_4895_ = v_arg_4915_;
goto _start;
}
else
{
return v___x_4896_;
}
}
case 11:
{
lean_object* v_struct_4918_; 
v_struct_4918_ = lean_ctor_get(v_e_4895_, 2);
v_e_4895_ = v_struct_4918_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4920_; uint8_t v___x_4921_; 
v_fvarId_4920_ = lean_ctor_get(v_e_4895_, 0);
v___x_4921_ = lean_name_eq(v_fvarId_4920_, v_fvarId_4894_);
return v___x_4921_;
}
default: 
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
}
}
v___jp_4897_:
{
uint8_t v___x_4900_; 
v___x_4900_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4894_, v_d_4898_);
if (v___x_4900_ == 0)
{
v_e_4895_ = v_b_4899_;
goto _start;
}
else
{
return v___x_4896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0___boxed(lean_object* v_fvarId_4923_, lean_object* v_e_4924_){
_start:
{
uint8_t v_res_4925_; lean_object* v_r_4926_; 
v_res_4925_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4923_, v_e_4924_);
lean_dec_ref(v_e_4924_);
lean_dec(v_fvarId_4923_);
v_r_4926_ = lean_box(v_res_4925_);
return v_r_4926_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* v_e_4927_, lean_object* v_fvarId_4928_){
_start:
{
uint8_t v___x_4929_; 
v___x_4929_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Expr_containsFVar_spec__0(v_fvarId_4928_, v_e_4927_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* v_e_4930_, lean_object* v_fvarId_4931_){
_start:
{
uint8_t v_res_4932_; lean_object* v_r_4933_; 
v_res_4932_ = l_Lean_Expr_containsFVar(v_e_4930_, v_fvarId_4931_);
lean_dec(v_fvarId_4931_);
lean_dec_ref(v_e_4930_);
v_r_4933_ = lean_box(v_res_4932_);
return v_r_4933_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(lean_object* v_p_4934_, lean_object* v_e_4935_){
_start:
{
uint8_t v___x_4936_; lean_object* v_d_4938_; lean_object* v_b_4939_; 
v___x_4936_ = l_Lean_Expr_hasExprMVar(v_e_4935_);
if (v___x_4936_ == 0)
{
lean_dec_ref(v_e_4935_);
lean_dec_ref(v_p_4934_);
return v___x_4936_;
}
else
{
switch(lean_obj_tag(v_e_4935_))
{
case 7:
{
lean_object* v_binderType_4942_; lean_object* v_body_4943_; 
v_binderType_4942_ = lean_ctor_get(v_e_4935_, 1);
lean_inc_ref(v_binderType_4942_);
v_body_4943_ = lean_ctor_get(v_e_4935_, 2);
lean_inc_ref(v_body_4943_);
lean_dec_ref_known(v_e_4935_, 3);
v_d_4938_ = v_binderType_4942_;
v_b_4939_ = v_body_4943_;
goto v___jp_4937_;
}
case 6:
{
lean_object* v_binderType_4944_; lean_object* v_body_4945_; 
v_binderType_4944_ = lean_ctor_get(v_e_4935_, 1);
lean_inc_ref(v_binderType_4944_);
v_body_4945_ = lean_ctor_get(v_e_4935_, 2);
lean_inc_ref(v_body_4945_);
lean_dec_ref_known(v_e_4935_, 3);
v_d_4938_ = v_binderType_4944_;
v_b_4939_ = v_body_4945_;
goto v___jp_4937_;
}
case 10:
{
lean_object* v_expr_4946_; 
v_expr_4946_ = lean_ctor_get(v_e_4935_, 1);
lean_inc_ref(v_expr_4946_);
lean_dec_ref_known(v_e_4935_, 2);
v_e_4935_ = v_expr_4946_;
goto _start;
}
case 8:
{
lean_object* v_type_4948_; lean_object* v_value_4949_; lean_object* v_body_4950_; uint8_t v___x_4951_; 
v_type_4948_ = lean_ctor_get(v_e_4935_, 1);
lean_inc_ref(v_type_4948_);
v_value_4949_ = lean_ctor_get(v_e_4935_, 2);
lean_inc_ref(v_value_4949_);
v_body_4950_ = lean_ctor_get(v_e_4935_, 3);
lean_inc_ref(v_body_4950_);
lean_dec_ref_known(v_e_4935_, 4);
lean_inc_ref(v_p_4934_);
v___x_4951_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4934_, v_type_4948_);
if (v___x_4951_ == 0)
{
uint8_t v___x_4952_; 
lean_inc_ref(v_p_4934_);
v___x_4952_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4934_, v_value_4949_);
if (v___x_4952_ == 0)
{
v_e_4935_ = v_body_4950_;
goto _start;
}
else
{
lean_dec_ref(v_body_4950_);
lean_dec_ref(v_p_4934_);
return v___x_4936_;
}
}
else
{
lean_dec_ref(v_body_4950_);
lean_dec_ref(v_value_4949_);
lean_dec_ref(v_p_4934_);
return v___x_4936_;
}
}
case 5:
{
lean_object* v_fn_4954_; lean_object* v_arg_4955_; uint8_t v___x_4956_; 
v_fn_4954_ = lean_ctor_get(v_e_4935_, 0);
lean_inc_ref(v_fn_4954_);
v_arg_4955_ = lean_ctor_get(v_e_4935_, 1);
lean_inc_ref(v_arg_4955_);
lean_dec_ref_known(v_e_4935_, 2);
lean_inc_ref(v_p_4934_);
v___x_4956_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4934_, v_fn_4954_);
if (v___x_4956_ == 0)
{
v_e_4935_ = v_arg_4955_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4955_);
lean_dec_ref(v_p_4934_);
return v___x_4936_;
}
}
case 11:
{
lean_object* v_struct_4958_; 
v_struct_4958_ = lean_ctor_get(v_e_4935_, 2);
lean_inc_ref(v_struct_4958_);
lean_dec_ref_known(v_e_4935_, 3);
v_e_4935_ = v_struct_4958_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
v_mvarId_4960_ = lean_ctor_get(v_e_4935_, 0);
lean_inc(v_mvarId_4960_);
lean_dec_ref_known(v_e_4935_, 1);
v___x_4961_ = lean_apply_1(v_p_4934_, v_mvarId_4960_);
v___x_4962_ = lean_unbox(v___x_4961_);
return v___x_4962_;
}
default: 
{
uint8_t v___x_4963_; 
lean_dec_ref(v_e_4935_);
lean_dec_ref(v_p_4934_);
v___x_4963_ = 0;
return v___x_4963_;
}
}
}
v___jp_4937_:
{
uint8_t v___x_4940_; 
lean_inc_ref(v_p_4934_);
v___x_4940_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4934_, v_d_4938_);
if (v___x_4940_ == 0)
{
v_e_4935_ = v_b_4939_;
goto _start;
}
else
{
lean_dec_ref(v_b_4939_);
lean_dec_ref(v_p_4934_);
return v___x_4936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___boxed(lean_object* v_p_4964_, lean_object* v_e_4965_){
_start:
{
uint8_t v_res_4966_; lean_object* v_r_4967_; 
v_res_4966_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4964_, v_e_4965_);
v_r_4967_ = lean_box(v_res_4966_);
return v_r_4967_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyMVar(lean_object* v_e_4968_, lean_object* v_p_4969_){
_start:
{
uint8_t v___x_4970_; 
v___x_4970_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit(v_p_4969_, v_e_4968_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyMVar___boxed(lean_object* v_e_4971_, lean_object* v_p_4972_){
_start:
{
uint8_t v_res_4973_; lean_object* v_r_4974_; 
v_res_4973_ = l_Lean_Expr_hasAnyMVar(v_e_4971_, v_p_4972_);
v_r_4974_ = lean_box(v_res_4973_);
return v_r_4974_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(lean_object* v_mvarId_4975_, lean_object* v_e_4976_){
_start:
{
uint8_t v___x_4977_; lean_object* v_d_4979_; lean_object* v_b_4980_; 
v___x_4977_ = l_Lean_Expr_hasExprMVar(v_e_4976_);
if (v___x_4977_ == 0)
{
return v___x_4977_;
}
else
{
switch(lean_obj_tag(v_e_4976_))
{
case 7:
{
lean_object* v_binderType_4983_; lean_object* v_body_4984_; 
v_binderType_4983_ = lean_ctor_get(v_e_4976_, 1);
v_body_4984_ = lean_ctor_get(v_e_4976_, 2);
v_d_4979_ = v_binderType_4983_;
v_b_4980_ = v_body_4984_;
goto v___jp_4978_;
}
case 6:
{
lean_object* v_binderType_4985_; lean_object* v_body_4986_; 
v_binderType_4985_ = lean_ctor_get(v_e_4976_, 1);
v_body_4986_ = lean_ctor_get(v_e_4976_, 2);
v_d_4979_ = v_binderType_4985_;
v_b_4980_ = v_body_4986_;
goto v___jp_4978_;
}
case 10:
{
lean_object* v_expr_4987_; 
v_expr_4987_ = lean_ctor_get(v_e_4976_, 1);
v_e_4976_ = v_expr_4987_;
goto _start;
}
case 8:
{
lean_object* v_type_4989_; lean_object* v_value_4990_; lean_object* v_body_4991_; uint8_t v___x_4992_; 
v_type_4989_ = lean_ctor_get(v_e_4976_, 1);
v_value_4990_ = lean_ctor_get(v_e_4976_, 2);
v_body_4991_ = lean_ctor_get(v_e_4976_, 3);
v___x_4992_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4975_, v_type_4989_);
if (v___x_4992_ == 0)
{
uint8_t v___x_4993_; 
v___x_4993_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4975_, v_value_4990_);
if (v___x_4993_ == 0)
{
v_e_4976_ = v_body_4991_;
goto _start;
}
else
{
return v___x_4977_;
}
}
else
{
return v___x_4977_;
}
}
case 5:
{
lean_object* v_fn_4995_; lean_object* v_arg_4996_; uint8_t v___x_4997_; 
v_fn_4995_ = lean_ctor_get(v_e_4976_, 0);
v_arg_4996_ = lean_ctor_get(v_e_4976_, 1);
v___x_4997_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4975_, v_fn_4995_);
if (v___x_4997_ == 0)
{
v_e_4976_ = v_arg_4996_;
goto _start;
}
else
{
return v___x_4977_;
}
}
case 11:
{
lean_object* v_struct_4999_; 
v_struct_4999_ = lean_ctor_get(v_e_4976_, 2);
v_e_4976_ = v_struct_4999_;
goto _start;
}
case 2:
{
lean_object* v_mvarId_5001_; uint8_t v___x_5002_; 
v_mvarId_5001_ = lean_ctor_get(v_e_4976_, 0);
v___x_5002_ = lean_name_eq(v_mvarId_5001_, v_mvarId_4975_);
return v___x_5002_;
}
default: 
{
uint8_t v___x_5003_; 
v___x_5003_ = 0;
return v___x_5003_;
}
}
}
v___jp_4978_:
{
uint8_t v___x_4981_; 
v___x_4981_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_4975_, v_d_4979_);
if (v___x_4981_ == 0)
{
v_e_4976_ = v_b_4980_;
goto _start;
}
else
{
return v___x_4977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0___boxed(lean_object* v_mvarId_5004_, lean_object* v_e_5005_){
_start:
{
uint8_t v_res_5006_; lean_object* v_r_5007_; 
v_res_5006_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5004_, v_e_5005_);
lean_dec_ref(v_e_5005_);
lean_dec(v_mvarId_5004_);
v_r_5007_ = lean_box(v_res_5006_);
return v_r_5007_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_containsMVar(lean_object* v_e_5008_, lean_object* v_mvarId_5009_){
_start:
{
uint8_t v___x_5010_; 
v___x_5010_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyMVar_visit___at___00Lean_Expr_containsMVar_spec__0(v_mvarId_5009_, v_e_5008_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_containsMVar___boxed(lean_object* v_e_5011_, lean_object* v_mvarId_5012_){
_start:
{
uint8_t v_res_5013_; lean_object* v_r_5014_; 
v_res_5013_ = l_Lean_Expr_containsMVar(v_e_5011_, v_mvarId_5012_);
lean_dec(v_mvarId_5012_);
lean_dec_ref(v_e_5011_);
v_r_5014_ = lean_box(v_res_5013_);
return v_r_5014_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5016_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__2));
v___x_5017_ = lean_unsigned_to_nat(18u);
v___x_5018_ = lean_unsigned_to_nat(1906u);
v___x_5019_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__0));
v___x_5020_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5021_ = l_mkPanicMessageWithDecl(v___x_5020_, v___x_5019_, v___x_5018_, v___x_5017_, v___x_5016_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* v_e_5022_, lean_object* v_newFn_5023_, lean_object* v_newArg_5024_){
_start:
{
if (lean_obj_tag(v_e_5022_) == 5)
{
lean_object* v_fn_5025_; lean_object* v_arg_5026_; size_t v___x_5027_; size_t v___x_5028_; uint8_t v___x_5029_; 
v_fn_5025_ = lean_ctor_get(v_e_5022_, 0);
v_arg_5026_ = lean_ctor_get(v_e_5022_, 1);
v___x_5027_ = lean_ptr_addr(v_fn_5025_);
v___x_5028_ = lean_ptr_addr(v_newFn_5023_);
v___x_5029_ = lean_usize_dec_eq(v___x_5027_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; 
v___x_5030_ = l_Lean_Expr_app___override(v_newFn_5023_, v_newArg_5024_);
return v___x_5030_;
}
else
{
size_t v___x_5031_; size_t v___x_5032_; uint8_t v___x_5033_; 
v___x_5031_ = lean_ptr_addr(v_arg_5026_);
v___x_5032_ = lean_ptr_addr(v_newArg_5024_);
v___x_5033_ = lean_usize_dec_eq(v___x_5031_, v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_Expr_app___override(v_newFn_5023_, v_newArg_5024_);
return v___x_5034_;
}
else
{
lean_dec_ref(v_newArg_5024_);
lean_dec_ref(v_newFn_5023_);
lean_inc_ref(v_e_5022_);
return v_e_5022_;
}
}
}
else
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
lean_dec_ref(v_newArg_5024_);
lean_dec_ref(v_newFn_5023_);
v___x_5035_ = l_Lean_instInhabitedExpr;
v___x_5036_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
v___x_5037_ = l_panic___redArg(v___x_5035_, v___x_5036_);
return v___x_5037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* v_e_5038_, lean_object* v_newFn_5039_, lean_object* v_newArg_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(v_e_5038_, v_newFn_5039_, v_newArg_5040_);
lean_dec_ref(v_e_5038_);
return v_res_5041_;
}
}
static lean_object* _init_l_Lean_Expr_updateFVar_x21___closed__1(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5043_ = ((lean_object*)(l_Lean_Expr_fvarId_x21___closed__1));
v___x_5044_ = lean_unsigned_to_nat(20u);
v___x_5045_ = lean_unsigned_to_nat(1917u);
v___x_5046_ = ((lean_object*)(l_Lean_Expr_updateFVar_x21___closed__0));
v___x_5047_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5048_ = l_mkPanicMessageWithDecl(v___x_5047_, v___x_5046_, v___x_5045_, v___x_5044_, v___x_5043_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21(lean_object* v_e_5049_, lean_object* v_fvarIdNew_5050_){
_start:
{
if (lean_obj_tag(v_e_5049_) == 1)
{
lean_object* v_fvarId_5051_; uint8_t v___x_5052_; 
v_fvarId_5051_ = lean_ctor_get(v_e_5049_, 0);
v___x_5052_ = lean_name_eq(v_fvarId_5051_, v_fvarIdNew_5050_);
if (v___x_5052_ == 0)
{
lean_object* v___x_5053_; 
v___x_5053_ = l_Lean_Expr_fvar___override(v_fvarIdNew_5050_);
return v___x_5053_;
}
else
{
lean_dec(v_fvarIdNew_5050_);
lean_inc_ref(v_e_5049_);
return v_e_5049_;
}
}
else
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
lean_dec(v_fvarIdNew_5050_);
v___x_5054_ = l_Lean_instInhabitedExpr;
v___x_5055_ = lean_obj_once(&l_Lean_Expr_updateFVar_x21___closed__1, &l_Lean_Expr_updateFVar_x21___closed__1_once, _init_l_Lean_Expr_updateFVar_x21___closed__1);
v___x_5056_ = l_panic___redArg(v___x_5054_, v___x_5055_);
return v___x_5056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFVar_x21___boxed(lean_object* v_e_5057_, lean_object* v_fvarIdNew_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_Expr_updateFVar_x21(v_e_5057_, v_fvarIdNew_5058_);
lean_dec_ref(v_e_5057_);
return v_res_5059_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5061_ = ((lean_object*)(l_Lean_Expr_constName_x21___closed__1));
v___x_5062_ = lean_unsigned_to_nat(18u);
v___x_5063_ = lean_unsigned_to_nat(1922u);
v___x_5064_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__0));
v___x_5065_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5066_ = l_mkPanicMessageWithDecl(v___x_5065_, v___x_5064_, v___x_5063_, v___x_5062_, v___x_5061_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* v_e_5067_, lean_object* v_newLevels_5068_){
_start:
{
if (lean_obj_tag(v_e_5067_) == 4)
{
lean_object* v_declName_5069_; lean_object* v_us_5070_; uint8_t v___x_5071_; 
v_declName_5069_ = lean_ctor_get(v_e_5067_, 0);
v_us_5070_ = lean_ctor_get(v_e_5067_, 1);
v___x_5071_ = l_ptrEqList___redArg(v_us_5070_, v_newLevels_5068_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; 
lean_inc(v_declName_5069_);
lean_dec_ref_known(v_e_5067_, 2);
v___x_5072_ = l_Lean_Expr_const___override(v_declName_5069_, v_newLevels_5068_);
return v___x_5072_;
}
else
{
lean_dec(v_newLevels_5068_);
return v_e_5067_;
}
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
lean_dec(v_newLevels_5068_);
lean_dec_ref(v_e_5067_);
v___x_5073_ = l_Lean_instInhabitedExpr;
v___x_5074_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
v___x_5075_ = l_panic___redArg(v___x_5073_, v___x_5074_);
return v___x_5075_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5078_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1));
v___x_5079_ = lean_unsigned_to_nat(14u);
v___x_5080_ = lean_unsigned_to_nat(1933u);
v___x_5081_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__0));
v___x_5082_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5083_ = l_mkPanicMessageWithDecl(v___x_5082_, v___x_5081_, v___x_5080_, v___x_5079_, v___x_5078_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* v_e_5084_, lean_object* v_u_x27_5085_){
_start:
{
if (lean_obj_tag(v_e_5084_) == 3)
{
lean_object* v_u_5086_; size_t v___x_5087_; size_t v___x_5088_; uint8_t v___x_5089_; 
v_u_5086_ = lean_ctor_get(v_e_5084_, 0);
v___x_5087_ = lean_ptr_addr(v_u_5086_);
v___x_5088_ = lean_ptr_addr(v_u_x27_5085_);
v___x_5089_ = lean_usize_dec_eq(v___x_5087_, v___x_5088_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Lean_Expr_sort___override(v_u_x27_5085_);
return v___x_5090_;
}
else
{
lean_dec(v_u_x27_5085_);
lean_inc_ref(v_e_5084_);
return v_e_5084_;
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec(v_u_x27_5085_);
v___x_5091_ = l_Lean_instInhabitedExpr;
v___x_5092_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
v___x_5093_ = l_panic___redArg(v___x_5091_, v___x_5092_);
return v___x_5093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* v_e_5094_, lean_object* v_u_x27_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(v_e_5094_, v_u_x27_5095_);
lean_dec_ref(v_e_5094_);
return v_res_5096_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5099_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1));
v___x_5100_ = lean_unsigned_to_nat(17u);
v___x_5101_ = lean_unsigned_to_nat(1944u);
v___x_5102_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__0));
v___x_5103_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5104_ = l_mkPanicMessageWithDecl(v___x_5103_, v___x_5102_, v___x_5101_, v___x_5100_, v___x_5099_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* v_e_5105_, lean_object* v_newExpr_5106_){
_start:
{
if (lean_obj_tag(v_e_5105_) == 10)
{
lean_object* v_data_5107_; lean_object* v_expr_5108_; size_t v___x_5109_; size_t v___x_5110_; uint8_t v___x_5111_; 
v_data_5107_ = lean_ctor_get(v_e_5105_, 0);
v_expr_5108_ = lean_ctor_get(v_e_5105_, 1);
v___x_5109_ = lean_ptr_addr(v_expr_5108_);
v___x_5110_ = lean_ptr_addr(v_newExpr_5106_);
v___x_5111_ = lean_usize_dec_eq(v___x_5109_, v___x_5110_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
lean_inc(v_data_5107_);
lean_dec_ref_known(v_e_5105_, 2);
v___x_5112_ = l_Lean_Expr_mdata___override(v_data_5107_, v_newExpr_5106_);
return v___x_5112_;
}
else
{
lean_dec_ref(v_newExpr_5106_);
return v_e_5105_;
}
}
else
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
lean_dec_ref(v_newExpr_5106_);
lean_dec_ref(v_e_5105_);
v___x_5113_ = l_Lean_instInhabitedExpr;
v___x_5114_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
v___x_5115_ = l_panic___redArg(v___x_5113_, v___x_5114_);
return v___x_5115_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5118_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1));
v___x_5119_ = lean_unsigned_to_nat(18u);
v___x_5120_ = lean_unsigned_to_nat(1955u);
v___x_5121_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__0));
v___x_5122_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5123_ = l_mkPanicMessageWithDecl(v___x_5122_, v___x_5121_, v___x_5120_, v___x_5119_, v___x_5118_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* v_e_5124_, lean_object* v_newExpr_5125_){
_start:
{
if (lean_obj_tag(v_e_5124_) == 11)
{
lean_object* v_typeName_5126_; lean_object* v_idx_5127_; lean_object* v_struct_5128_; size_t v___x_5129_; size_t v___x_5130_; uint8_t v___x_5131_; 
v_typeName_5126_ = lean_ctor_get(v_e_5124_, 0);
v_idx_5127_ = lean_ctor_get(v_e_5124_, 1);
v_struct_5128_ = lean_ctor_get(v_e_5124_, 2);
v___x_5129_ = lean_ptr_addr(v_struct_5128_);
v___x_5130_ = lean_ptr_addr(v_newExpr_5125_);
v___x_5131_ = lean_usize_dec_eq(v___x_5129_, v___x_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; 
lean_inc(v_idx_5127_);
lean_inc(v_typeName_5126_);
lean_dec_ref_known(v_e_5124_, 3);
v___x_5132_ = l_Lean_Expr_proj___override(v_typeName_5126_, v_idx_5127_, v_newExpr_5125_);
return v___x_5132_;
}
else
{
lean_dec_ref(v_newExpr_5125_);
return v_e_5124_;
}
}
else
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
lean_dec_ref(v_newExpr_5125_);
lean_dec_ref(v_e_5124_);
v___x_5133_ = l_Lean_instInhabitedExpr;
v___x_5134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
v___x_5135_ = l_panic___redArg(v___x_5133_, v___x_5134_);
return v___x_5135_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5138_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5139_ = lean_unsigned_to_nat(23u);
v___x_5140_ = lean_unsigned_to_nat(1970u);
v___x_5141_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__0));
v___x_5142_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5143_ = l_mkPanicMessageWithDecl(v___x_5142_, v___x_5141_, v___x_5140_, v___x_5139_, v___x_5138_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* v_e_5144_, uint8_t v_newBinfo_5145_, lean_object* v_newDomain_5146_, lean_object* v_newBody_5147_){
_start:
{
if (lean_obj_tag(v_e_5144_) == 7)
{
lean_object* v_binderName_5148_; lean_object* v_binderType_5149_; lean_object* v_body_5150_; uint8_t v_binderInfo_5151_; size_t v___x_5152_; size_t v___x_5153_; uint8_t v___x_5154_; 
v_binderName_5148_ = lean_ctor_get(v_e_5144_, 0);
v_binderType_5149_ = lean_ctor_get(v_e_5144_, 1);
v_body_5150_ = lean_ctor_get(v_e_5144_, 2);
v_binderInfo_5151_ = lean_ctor_get_uint8(v_e_5144_, sizeof(void*)*3 + 8);
v___x_5152_ = lean_ptr_addr(v_binderType_5149_);
v___x_5153_ = lean_ptr_addr(v_newDomain_5146_);
v___x_5154_ = lean_usize_dec_eq(v___x_5152_, v___x_5153_);
if (v___x_5154_ == 0)
{
lean_object* v___x_5155_; 
lean_inc(v_binderName_5148_);
lean_dec_ref_known(v_e_5144_, 3);
v___x_5155_ = l_Lean_Expr_forallE___override(v_binderName_5148_, v_newDomain_5146_, v_newBody_5147_, v_newBinfo_5145_);
return v___x_5155_;
}
else
{
size_t v___x_5156_; size_t v___x_5157_; uint8_t v___x_5158_; 
v___x_5156_ = lean_ptr_addr(v_body_5150_);
v___x_5157_ = lean_ptr_addr(v_newBody_5147_);
v___x_5158_ = lean_usize_dec_eq(v___x_5156_, v___x_5157_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; 
lean_inc(v_binderName_5148_);
lean_dec_ref_known(v_e_5144_, 3);
v___x_5159_ = l_Lean_Expr_forallE___override(v_binderName_5148_, v_newDomain_5146_, v_newBody_5147_, v_newBinfo_5145_);
return v___x_5159_;
}
else
{
uint8_t v___x_5160_; 
v___x_5160_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5151_, v_newBinfo_5145_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; 
lean_inc(v_binderName_5148_);
lean_dec_ref_known(v_e_5144_, 3);
v___x_5161_ = l_Lean_Expr_forallE___override(v_binderName_5148_, v_newDomain_5146_, v_newBody_5147_, v_newBinfo_5145_);
return v___x_5161_;
}
else
{
lean_dec_ref(v_newBody_5147_);
lean_dec_ref(v_newDomain_5146_);
return v_e_5144_;
}
}
}
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
lean_dec_ref(v_newBody_5147_);
lean_dec_ref(v_newDomain_5146_);
lean_dec_ref(v_e_5144_);
v___x_5162_ = l_Lean_instInhabitedExpr;
v___x_5163_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
v___x_5164_ = l_panic___redArg(v___x_5162_, v___x_5163_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* v_e_5165_, lean_object* v_newBinfo_5166_, lean_object* v_newDomain_5167_, lean_object* v_newBody_5168_){
_start:
{
uint8_t v_newBinfo_boxed_5169_; lean_object* v_res_5170_; 
v_newBinfo_boxed_5169_ = lean_unbox(v_newBinfo_5166_);
v_res_5170_ = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(v_e_5165_, v_newBinfo_boxed_5169_, v_newDomain_5167_, v_newBody_5168_);
return v_res_5170_;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1(void){
_start:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5172_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1));
v___x_5173_ = lean_unsigned_to_nat(24u);
v___x_5174_ = lean_unsigned_to_nat(1981u);
v___x_5175_ = ((lean_object*)(l_Lean_Expr_updateForallE_x21___closed__0));
v___x_5176_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5177_ = l_mkPanicMessageWithDecl(v___x_5176_, v___x_5175_, v___x_5174_, v___x_5173_, v___x_5172_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* v_e_5178_, lean_object* v_newDomain_5179_, lean_object* v_newBody_5180_){
_start:
{
if (lean_obj_tag(v_e_5178_) == 7)
{
lean_object* v_binderName_5181_; lean_object* v_binderType_5182_; lean_object* v_body_5183_; uint8_t v_binderInfo_5184_; size_t v___x_5185_; size_t v___x_5186_; uint8_t v___x_5187_; 
v_binderName_5181_ = lean_ctor_get(v_e_5178_, 0);
v_binderType_5182_ = lean_ctor_get(v_e_5178_, 1);
v_body_5183_ = lean_ctor_get(v_e_5178_, 2);
v_binderInfo_5184_ = lean_ctor_get_uint8(v_e_5178_, sizeof(void*)*3 + 8);
v___x_5185_ = lean_ptr_addr(v_binderType_5182_);
v___x_5186_ = lean_ptr_addr(v_newDomain_5179_);
v___x_5187_ = lean_usize_dec_eq(v___x_5185_, v___x_5186_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; 
lean_inc(v_binderName_5181_);
lean_dec_ref_known(v_e_5178_, 3);
v___x_5188_ = l_Lean_Expr_forallE___override(v_binderName_5181_, v_newDomain_5179_, v_newBody_5180_, v_binderInfo_5184_);
return v___x_5188_;
}
else
{
size_t v___x_5189_; size_t v___x_5190_; uint8_t v___x_5191_; 
v___x_5189_ = lean_ptr_addr(v_body_5183_);
v___x_5190_ = lean_ptr_addr(v_newBody_5180_);
v___x_5191_ = lean_usize_dec_eq(v___x_5189_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_object* v___x_5192_; 
lean_inc(v_binderName_5181_);
lean_dec_ref_known(v_e_5178_, 3);
v___x_5192_ = l_Lean_Expr_forallE___override(v_binderName_5181_, v_newDomain_5179_, v_newBody_5180_, v_binderInfo_5184_);
return v___x_5192_;
}
else
{
uint8_t v___x_5193_; 
v___x_5193_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5184_, v_binderInfo_5184_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; 
lean_inc(v_binderName_5181_);
lean_dec_ref_known(v_e_5178_, 3);
v___x_5194_ = l_Lean_Expr_forallE___override(v_binderName_5181_, v_newDomain_5179_, v_newBody_5180_, v_binderInfo_5184_);
return v___x_5194_;
}
else
{
lean_dec_ref(v_newBody_5180_);
lean_dec_ref(v_newDomain_5179_);
return v_e_5178_;
}
}
}
}
else
{
lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
lean_dec_ref(v_newBody_5180_);
lean_dec_ref(v_newDomain_5179_);
lean_dec_ref(v_e_5178_);
v___x_5195_ = l_Lean_instInhabitedExpr;
v___x_5196_ = lean_obj_once(&l_Lean_Expr_updateForallE_x21___closed__1, &l_Lean_Expr_updateForallE_x21___closed__1_once, _init_l_Lean_Expr_updateForallE_x21___closed__1);
v___x_5197_ = l_panic___redArg(v___x_5195_, v___x_5196_);
return v___x_5197_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2(void){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5200_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5201_ = lean_unsigned_to_nat(19u);
v___x_5202_ = lean_unsigned_to_nat(1990u);
v___x_5203_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__0));
v___x_5204_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5205_ = l_mkPanicMessageWithDecl(v___x_5204_, v___x_5203_, v___x_5202_, v___x_5201_, v___x_5200_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* v_e_5206_, uint8_t v_newBinfo_5207_, lean_object* v_newDomain_5208_, lean_object* v_newBody_5209_){
_start:
{
if (lean_obj_tag(v_e_5206_) == 6)
{
lean_object* v_binderName_5210_; lean_object* v_binderType_5211_; lean_object* v_body_5212_; uint8_t v_binderInfo_5213_; size_t v___x_5214_; size_t v___x_5215_; uint8_t v___x_5216_; 
v_binderName_5210_ = lean_ctor_get(v_e_5206_, 0);
v_binderType_5211_ = lean_ctor_get(v_e_5206_, 1);
v_body_5212_ = lean_ctor_get(v_e_5206_, 2);
v_binderInfo_5213_ = lean_ctor_get_uint8(v_e_5206_, sizeof(void*)*3 + 8);
v___x_5214_ = lean_ptr_addr(v_binderType_5211_);
v___x_5215_ = lean_ptr_addr(v_newDomain_5208_);
v___x_5216_ = lean_usize_dec_eq(v___x_5214_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; 
lean_inc(v_binderName_5210_);
lean_dec_ref_known(v_e_5206_, 3);
v___x_5217_ = l_Lean_Expr_lam___override(v_binderName_5210_, v_newDomain_5208_, v_newBody_5209_, v_newBinfo_5207_);
return v___x_5217_;
}
else
{
size_t v___x_5218_; size_t v___x_5219_; uint8_t v___x_5220_; 
v___x_5218_ = lean_ptr_addr(v_body_5212_);
v___x_5219_ = lean_ptr_addr(v_newBody_5209_);
v___x_5220_ = lean_usize_dec_eq(v___x_5218_, v___x_5219_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
lean_inc(v_binderName_5210_);
lean_dec_ref_known(v_e_5206_, 3);
v___x_5221_ = l_Lean_Expr_lam___override(v_binderName_5210_, v_newDomain_5208_, v_newBody_5209_, v_newBinfo_5207_);
return v___x_5221_;
}
else
{
uint8_t v___x_5222_; 
v___x_5222_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5213_, v_newBinfo_5207_);
if (v___x_5222_ == 0)
{
lean_object* v___x_5223_; 
lean_inc(v_binderName_5210_);
lean_dec_ref_known(v_e_5206_, 3);
v___x_5223_ = l_Lean_Expr_lam___override(v_binderName_5210_, v_newDomain_5208_, v_newBody_5209_, v_newBinfo_5207_);
return v___x_5223_;
}
else
{
lean_dec_ref(v_newBody_5209_);
lean_dec_ref(v_newDomain_5208_);
return v_e_5206_;
}
}
}
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_dec_ref(v_newBody_5209_);
lean_dec_ref(v_newDomain_5208_);
lean_dec_ref(v_e_5206_);
v___x_5224_ = l_Lean_instInhabitedExpr;
v___x_5225_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2, &l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
v___x_5226_ = l_panic___redArg(v___x_5224_, v___x_5225_);
return v___x_5226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* v_e_5227_, lean_object* v_newBinfo_5228_, lean_object* v_newDomain_5229_, lean_object* v_newBody_5230_){
_start:
{
uint8_t v_newBinfo_boxed_5231_; lean_object* v_res_5232_; 
v_newBinfo_boxed_5231_ = lean_unbox(v_newBinfo_5228_);
v_res_5232_ = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(v_e_5227_, v_newBinfo_boxed_5231_, v_newDomain_5229_, v_newBody_5230_);
return v_res_5232_;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1(void){
_start:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5234_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1));
v___x_5235_ = lean_unsigned_to_nat(20u);
v___x_5236_ = lean_unsigned_to_nat(2001u);
v___x_5237_ = ((lean_object*)(l_Lean_Expr_updateLambdaE_x21___closed__0));
v___x_5238_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5239_ = l_mkPanicMessageWithDecl(v___x_5238_, v___x_5237_, v___x_5236_, v___x_5235_, v___x_5234_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* v_e_5240_, lean_object* v_newDomain_5241_, lean_object* v_newBody_5242_){
_start:
{
if (lean_obj_tag(v_e_5240_) == 6)
{
lean_object* v_binderName_5243_; lean_object* v_binderType_5244_; lean_object* v_body_5245_; uint8_t v_binderInfo_5246_; size_t v___x_5247_; size_t v___x_5248_; uint8_t v___x_5249_; 
v_binderName_5243_ = lean_ctor_get(v_e_5240_, 0);
v_binderType_5244_ = lean_ctor_get(v_e_5240_, 1);
v_body_5245_ = lean_ctor_get(v_e_5240_, 2);
v_binderInfo_5246_ = lean_ctor_get_uint8(v_e_5240_, sizeof(void*)*3 + 8);
v___x_5247_ = lean_ptr_addr(v_binderType_5244_);
v___x_5248_ = lean_ptr_addr(v_newDomain_5241_);
v___x_5249_ = lean_usize_dec_eq(v___x_5247_, v___x_5248_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; 
lean_inc(v_binderName_5243_);
lean_dec_ref_known(v_e_5240_, 3);
v___x_5250_ = l_Lean_Expr_lam___override(v_binderName_5243_, v_newDomain_5241_, v_newBody_5242_, v_binderInfo_5246_);
return v___x_5250_;
}
else
{
size_t v___x_5251_; size_t v___x_5252_; uint8_t v___x_5253_; 
v___x_5251_ = lean_ptr_addr(v_body_5245_);
v___x_5252_ = lean_ptr_addr(v_newBody_5242_);
v___x_5253_ = lean_usize_dec_eq(v___x_5251_, v___x_5252_);
if (v___x_5253_ == 0)
{
lean_object* v___x_5254_; 
lean_inc(v_binderName_5243_);
lean_dec_ref_known(v_e_5240_, 3);
v___x_5254_ = l_Lean_Expr_lam___override(v_binderName_5243_, v_newDomain_5241_, v_newBody_5242_, v_binderInfo_5246_);
return v___x_5254_;
}
else
{
uint8_t v___x_5255_; 
v___x_5255_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5246_, v_binderInfo_5246_);
if (v___x_5255_ == 0)
{
lean_object* v___x_5256_; 
lean_inc(v_binderName_5243_);
lean_dec_ref_known(v_e_5240_, 3);
v___x_5256_ = l_Lean_Expr_lam___override(v_binderName_5243_, v_newDomain_5241_, v_newBody_5242_, v_binderInfo_5246_);
return v___x_5256_;
}
else
{
lean_dec_ref(v_newBody_5242_);
lean_dec_ref(v_newDomain_5241_);
return v_e_5240_;
}
}
}
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; 
lean_dec_ref(v_newBody_5242_);
lean_dec_ref(v_newDomain_5241_);
lean_dec_ref(v_e_5240_);
v___x_5257_ = l_Lean_instInhabitedExpr;
v___x_5258_ = lean_obj_once(&l_Lean_Expr_updateLambdaE_x21___closed__1, &l_Lean_Expr_updateLambdaE_x21___closed__1_once, _init_l_Lean_Expr_updateLambdaE_x21___closed__1);
v___x_5259_ = l_panic___redArg(v___x_5257_, v___x_5258_);
return v___x_5259_;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5261_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5262_ = lean_unsigned_to_nat(22u);
v___x_5263_ = lean_unsigned_to_nat(2010u);
v___x_5264_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__0));
v___x_5265_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5266_ = l_mkPanicMessageWithDecl(v___x_5265_, v___x_5264_, v___x_5263_, v___x_5262_, v___x_5261_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* v_e_5267_, lean_object* v_newType_5268_, lean_object* v_newVal_5269_, lean_object* v_newBody_5270_, uint8_t v_newNondep_5271_){
_start:
{
if (lean_obj_tag(v_e_5267_) == 8)
{
lean_object* v_declName_5272_; lean_object* v_type_5273_; lean_object* v_value_5274_; lean_object* v_body_5275_; uint8_t v_nondep_5276_; size_t v___x_5277_; size_t v___x_5278_; uint8_t v___x_5279_; 
v_declName_5272_ = lean_ctor_get(v_e_5267_, 0);
v_type_5273_ = lean_ctor_get(v_e_5267_, 1);
v_value_5274_ = lean_ctor_get(v_e_5267_, 2);
v_body_5275_ = lean_ctor_get(v_e_5267_, 3);
v_nondep_5276_ = lean_ctor_get_uint8(v_e_5267_, sizeof(void*)*4 + 8);
v___x_5277_ = lean_ptr_addr(v_type_5273_);
v___x_5278_ = lean_ptr_addr(v_newType_5268_);
v___x_5279_ = lean_usize_dec_eq(v___x_5277_, v___x_5278_);
if (v___x_5279_ == 0)
{
lean_object* v___x_5280_; 
lean_inc(v_declName_5272_);
lean_dec_ref_known(v_e_5267_, 4);
v___x_5280_ = l_Lean_Expr_letE___override(v_declName_5272_, v_newType_5268_, v_newVal_5269_, v_newBody_5270_, v_newNondep_5271_);
return v___x_5280_;
}
else
{
size_t v___x_5281_; size_t v___x_5282_; uint8_t v___x_5283_; 
v___x_5281_ = lean_ptr_addr(v_value_5274_);
v___x_5282_ = lean_ptr_addr(v_newVal_5269_);
v___x_5283_ = lean_usize_dec_eq(v___x_5281_, v___x_5282_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; 
lean_inc(v_declName_5272_);
lean_dec_ref_known(v_e_5267_, 4);
v___x_5284_ = l_Lean_Expr_letE___override(v_declName_5272_, v_newType_5268_, v_newVal_5269_, v_newBody_5270_, v_newNondep_5271_);
return v___x_5284_;
}
else
{
size_t v___x_5285_; size_t v___x_5286_; uint8_t v___x_5287_; 
v___x_5285_ = lean_ptr_addr(v_body_5275_);
v___x_5286_ = lean_ptr_addr(v_newBody_5270_);
v___x_5287_ = lean_usize_dec_eq(v___x_5285_, v___x_5286_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; 
lean_inc(v_declName_5272_);
lean_dec_ref_known(v_e_5267_, 4);
v___x_5288_ = l_Lean_Expr_letE___override(v_declName_5272_, v_newType_5268_, v_newVal_5269_, v_newBody_5270_, v_newNondep_5271_);
return v___x_5288_;
}
else
{
if (v_newNondep_5271_ == 0)
{
if (v_nondep_5276_ == 0)
{
lean_dec_ref(v_newBody_5270_);
lean_dec_ref(v_newVal_5269_);
lean_dec_ref(v_newType_5268_);
return v_e_5267_;
}
else
{
lean_object* v___x_5289_; 
lean_inc(v_declName_5272_);
lean_dec_ref_known(v_e_5267_, 4);
v___x_5289_ = l_Lean_Expr_letE___override(v_declName_5272_, v_newType_5268_, v_newVal_5269_, v_newBody_5270_, v_newNondep_5271_);
return v___x_5289_;
}
}
else
{
if (v_nondep_5276_ == 0)
{
lean_object* v___x_5290_; 
lean_inc(v_declName_5272_);
lean_dec_ref_known(v_e_5267_, 4);
v___x_5290_ = l_Lean_Expr_letE___override(v_declName_5272_, v_newType_5268_, v_newVal_5269_, v_newBody_5270_, v_newNondep_5271_);
return v___x_5290_;
}
else
{
lean_dec_ref(v_newBody_5270_);
lean_dec_ref(v_newVal_5269_);
lean_dec_ref(v_newType_5268_);
return v_e_5267_;
}
}
}
}
}
}
else
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_dec_ref(v_newBody_5270_);
lean_dec_ref(v_newVal_5269_);
lean_dec_ref(v_newType_5268_);
lean_dec_ref(v_e_5267_);
v___x_5291_ = l_Lean_instInhabitedExpr;
v___x_5292_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1, &l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1_once, _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
v___x_5293_ = l_panic___redArg(v___x_5291_, v___x_5292_);
return v___x_5293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___boxed(lean_object* v_e_5294_, lean_object* v_newType_5295_, lean_object* v_newVal_5296_, lean_object* v_newBody_5297_, lean_object* v_newNondep_5298_){
_start:
{
uint8_t v_newNondep_boxed_5299_; lean_object* v_res_5300_; 
v_newNondep_boxed_5299_ = lean_unbox(v_newNondep_5298_);
v_res_5300_ = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(v_e_5294_, v_newType_5295_, v_newVal_5296_, v_newBody_5297_, v_newNondep_boxed_5299_);
return v_res_5300_;
}
}
static lean_object* _init_l_Lean_Expr_updateLetE_x21___closed__1(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5302_ = ((lean_object*)(l_Lean_Expr_letName_x21___closed__1));
v___x_5303_ = lean_unsigned_to_nat(27u);
v___x_5304_ = lean_unsigned_to_nat(2023u);
v___x_5305_ = ((lean_object*)(l_Lean_Expr_updateLetE_x21___closed__0));
v___x_5306_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_5307_ = l_mkPanicMessageWithDecl(v___x_5306_, v___x_5305_, v___x_5304_, v___x_5303_, v___x_5302_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetE_x21(lean_object* v_e_5308_, lean_object* v_newType_5309_, lean_object* v_newVal_5310_, lean_object* v_newBody_5311_){
_start:
{
if (lean_obj_tag(v_e_5308_) == 8)
{
lean_object* v_declName_5312_; lean_object* v_type_5313_; lean_object* v_value_5314_; lean_object* v_body_5315_; uint8_t v_nondep_5316_; size_t v___x_5317_; size_t v___x_5318_; uint8_t v___x_5319_; 
v_declName_5312_ = lean_ctor_get(v_e_5308_, 0);
v_type_5313_ = lean_ctor_get(v_e_5308_, 1);
v_value_5314_ = lean_ctor_get(v_e_5308_, 2);
v_body_5315_ = lean_ctor_get(v_e_5308_, 3);
v_nondep_5316_ = lean_ctor_get_uint8(v_e_5308_, sizeof(void*)*4 + 8);
v___x_5317_ = lean_ptr_addr(v_type_5313_);
v___x_5318_ = lean_ptr_addr(v_newType_5309_);
v___x_5319_ = lean_usize_dec_eq(v___x_5317_, v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
lean_inc(v_declName_5312_);
lean_dec_ref_known(v_e_5308_, 4);
v___x_5320_ = l_Lean_Expr_letE___override(v_declName_5312_, v_newType_5309_, v_newVal_5310_, v_newBody_5311_, v_nondep_5316_);
return v___x_5320_;
}
else
{
size_t v___x_5321_; size_t v___x_5322_; uint8_t v___x_5323_; 
v___x_5321_ = lean_ptr_addr(v_value_5314_);
v___x_5322_ = lean_ptr_addr(v_newVal_5310_);
v___x_5323_ = lean_usize_dec_eq(v___x_5321_, v___x_5322_);
if (v___x_5323_ == 0)
{
lean_object* v___x_5324_; 
lean_inc(v_declName_5312_);
lean_dec_ref_known(v_e_5308_, 4);
v___x_5324_ = l_Lean_Expr_letE___override(v_declName_5312_, v_newType_5309_, v_newVal_5310_, v_newBody_5311_, v_nondep_5316_);
return v___x_5324_;
}
else
{
size_t v___x_5325_; size_t v___x_5326_; uint8_t v___x_5327_; 
v___x_5325_ = lean_ptr_addr(v_body_5315_);
v___x_5326_ = lean_ptr_addr(v_newBody_5311_);
v___x_5327_ = lean_usize_dec_eq(v___x_5325_, v___x_5326_);
if (v___x_5327_ == 0)
{
lean_object* v___x_5328_; 
lean_inc(v_declName_5312_);
lean_dec_ref_known(v_e_5308_, 4);
v___x_5328_ = l_Lean_Expr_letE___override(v_declName_5312_, v_newType_5309_, v_newVal_5310_, v_newBody_5311_, v_nondep_5316_);
return v___x_5328_;
}
else
{
lean_dec_ref(v_newBody_5311_);
lean_dec_ref(v_newVal_5310_);
lean_dec_ref(v_newType_5309_);
return v_e_5308_;
}
}
}
}
else
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
lean_dec_ref(v_newBody_5311_);
lean_dec_ref(v_newVal_5310_);
lean_dec_ref(v_newType_5309_);
lean_dec_ref(v_e_5308_);
v___x_5329_ = l_Lean_instInhabitedExpr;
v___x_5330_ = lean_obj_once(&l_Lean_Expr_updateLetE_x21___closed__1, &l_Lean_Expr_updateLetE_x21___closed__1_once, _init_l_Lean_Expr_updateLetE_x21___closed__1);
v___x_5331_ = l_panic___redArg(v___x_5329_, v___x_5330_);
return v___x_5331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* v_x_5332_, lean_object* v_x_5333_){
_start:
{
if (lean_obj_tag(v_x_5332_) == 5)
{
lean_object* v_fn_5334_; lean_object* v_arg_5335_; lean_object* v___x_5336_; size_t v___x_5337_; size_t v___x_5338_; uint8_t v___x_5339_; 
v_fn_5334_ = lean_ctor_get(v_x_5332_, 0);
v_arg_5335_ = lean_ctor_get(v_x_5332_, 1);
lean_inc_ref(v_fn_5334_);
v___x_5336_ = l_Lean_Expr_updateFn(v_fn_5334_, v_x_5333_);
v___x_5337_ = lean_ptr_addr(v_fn_5334_);
v___x_5338_ = lean_ptr_addr(v___x_5336_);
v___x_5339_ = lean_usize_dec_eq(v___x_5337_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
lean_inc_ref(v_arg_5335_);
lean_dec_ref_known(v_x_5332_, 2);
v___x_5340_ = l_Lean_Expr_app___override(v___x_5336_, v_arg_5335_);
return v___x_5340_;
}
else
{
size_t v___x_5341_; size_t v___x_5342_; uint8_t v___x_5343_; 
v___x_5341_ = lean_ptr_addr(v_arg_5335_);
v___x_5342_ = lean_ptr_addr(v_arg_5335_);
v___x_5343_ = lean_usize_dec_eq(v___x_5341_, v___x_5342_);
if (v___x_5343_ == 0)
{
lean_object* v___x_5344_; 
lean_inc_ref(v_arg_5335_);
lean_dec_ref_known(v_x_5332_, 2);
v___x_5344_ = l_Lean_Expr_app___override(v___x_5336_, v_arg_5335_);
return v___x_5344_;
}
else
{
lean_dec_ref(v___x_5336_);
return v_x_5332_;
}
}
}
else
{
lean_dec_ref(v_x_5332_);
lean_inc_ref(v_x_5333_);
return v_x_5333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* v_x_5345_, lean_object* v_x_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Expr_updateFn(v_x_5345_, v_x_5346_);
lean_dec_ref(v_x_5346_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* v_e_5348_){
_start:
{
if (lean_obj_tag(v_e_5348_) == 6)
{
lean_object* v_binderName_5349_; lean_object* v_binderType_5350_; lean_object* v_body_5351_; uint8_t v_binderInfo_5352_; lean_object* v_b_x27_5353_; 
v_binderName_5349_ = lean_ctor_get(v_e_5348_, 0);
v_binderType_5350_ = lean_ctor_get(v_e_5348_, 1);
v_body_5351_ = lean_ctor_get(v_e_5348_, 2);
v_binderInfo_5352_ = lean_ctor_get_uint8(v_e_5348_, sizeof(void*)*3 + 8);
lean_inc_ref(v_body_5351_);
v_b_x27_5353_ = l_Lean_Expr_eta(v_body_5351_);
if (lean_obj_tag(v_b_x27_5353_) == 5)
{
lean_object* v_arg_5365_; 
v_arg_5365_ = lean_ctor_get(v_b_x27_5353_, 1);
if (lean_obj_tag(v_arg_5365_) == 0)
{
lean_object* v_fn_5366_; lean_object* v_deBruijnIndex_5367_; lean_object* v___x_5368_; uint8_t v___x_5369_; 
v_fn_5366_ = lean_ctor_get(v_b_x27_5353_, 0);
v_deBruijnIndex_5367_ = lean_ctor_get(v_arg_5365_, 0);
v___x_5368_ = lean_unsigned_to_nat(0u);
v___x_5369_ = lean_nat_dec_eq(v_deBruijnIndex_5367_, v___x_5368_);
if (v___x_5369_ == 0)
{
goto v___jp_5354_;
}
else
{
uint8_t v___x_5370_; 
v___x_5370_ = lean_expr_has_loose_bvar(v_fn_5366_, v___x_5368_);
if (v___x_5370_ == 0)
{
lean_object* v___x_5371_; lean_object* v___x_5372_; 
lean_inc_ref(v_fn_5366_);
lean_dec_ref_known(v_b_x27_5353_, 2);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5371_ = lean_unsigned_to_nat(1u);
v___x_5372_ = lean_expr_lower_loose_bvars(v_fn_5366_, v___x_5371_, v___x_5371_);
lean_dec_ref(v_fn_5366_);
return v___x_5372_;
}
else
{
size_t v___x_5373_; size_t v___x_5374_; uint8_t v___x_5375_; 
v___x_5373_ = lean_ptr_addr(v_binderType_5350_);
v___x_5374_ = lean_ptr_addr(v_binderType_5350_);
v___x_5375_ = lean_usize_dec_eq(v___x_5373_, v___x_5374_);
if (v___x_5375_ == 0)
{
lean_object* v___x_5376_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5376_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5376_;
}
else
{
size_t v___x_5377_; size_t v___x_5378_; uint8_t v___x_5379_; 
v___x_5377_ = lean_ptr_addr(v_body_5351_);
v___x_5378_ = lean_ptr_addr(v_b_x27_5353_);
v___x_5379_ = lean_usize_dec_eq(v___x_5377_, v___x_5378_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5380_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5380_;
}
else
{
uint8_t v___x_5381_; 
v___x_5381_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5352_, v_binderInfo_5352_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5382_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5382_;
}
else
{
lean_dec_ref_known(v_b_x27_5353_, 2);
return v_e_5348_;
}
}
}
}
}
}
else
{
goto v___jp_5354_;
}
}
else
{
goto v___jp_5354_;
}
v___jp_5354_:
{
size_t v___x_5355_; size_t v___x_5356_; uint8_t v___x_5357_; 
v___x_5355_ = lean_ptr_addr(v_binderType_5350_);
v___x_5356_ = lean_ptr_addr(v_binderType_5350_);
v___x_5357_ = lean_usize_dec_eq(v___x_5355_, v___x_5356_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5358_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5358_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5358_;
}
else
{
size_t v___x_5359_; size_t v___x_5360_; uint8_t v___x_5361_; 
v___x_5359_ = lean_ptr_addr(v_body_5351_);
v___x_5360_ = lean_ptr_addr(v_b_x27_5353_);
v___x_5361_ = lean_usize_dec_eq(v___x_5359_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_object* v___x_5362_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5362_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5362_;
}
else
{
uint8_t v___x_5363_; 
v___x_5363_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5352_, v_binderInfo_5352_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
lean_inc_ref(v_binderType_5350_);
lean_inc(v_binderName_5349_);
lean_dec_ref_known(v_e_5348_, 3);
v___x_5364_ = l_Lean_Expr_lam___override(v_binderName_5349_, v_binderType_5350_, v_b_x27_5353_, v_binderInfo_5352_);
return v___x_5364_;
}
else
{
lean_dec_ref(v_b_x27_5353_);
return v_e_5348_;
}
}
}
}
}
else
{
return v_e_5348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___redArg(lean_object* v_e_5383_, lean_object* v_optionName_5384_, lean_object* v_inst_5385_, lean_object* v_val_5386_){
_start:
{
lean_object* v_toDataValue_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v_toDataValue_5387_ = lean_ctor_get(v_inst_5385_, 0);
lean_inc_ref(v_toDataValue_5387_);
lean_dec_ref(v_inst_5385_);
v___x_5388_ = lean_box(0);
v___x_5389_ = lean_apply_1(v_toDataValue_5387_, v_val_5386_);
v___x_5390_ = l_Lean_KVMap_insert(v___x_5388_, v_optionName_5384_, v___x_5389_);
v___x_5391_ = l_Lean_Expr_mdata___override(v___x_5390_, v_e_5383_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* v_00_u03b1_5392_, lean_object* v_e_5393_, lean_object* v_optionName_5394_, lean_object* v_inst_5395_, lean_object* v_val_5396_){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = l_Lean_Expr_setOption___redArg(v_e_5393_, v_optionName_5394_, v_inst_5395_, v_val_5396_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(lean_object* v_e_5398_, lean_object* v_optionName_5399_, uint8_t v_val_5400_){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5401_ = lean_box(0);
v___x_5402_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5402_, 0, v_val_5400_);
v___x_5403_ = l_Lean_KVMap_insert(v___x_5401_, v_optionName_5399_, v___x_5402_);
v___x_5404_ = l_Lean_Expr_mdata___override(v___x_5403_, v_e_5398_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0___boxed(lean_object* v_e_5405_, lean_object* v_optionName_5406_, lean_object* v_val_5407_){
_start:
{
uint8_t v_val_boxed_5408_; lean_object* v_res_5409_; 
v_val_boxed_5408_ = lean_unbox(v_val_5407_);
v_res_5409_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5405_, v_optionName_5406_, v_val_boxed_5408_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* v_e_5415_, uint8_t v_flag_5416_){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5417_ = ((lean_object*)(l_Lean_Expr_setPPExplicit___closed__2));
v___x_5418_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5415_, v___x_5417_, v_flag_5416_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* v_e_5419_, lean_object* v_flag_5420_){
_start:
{
uint8_t v_flag_boxed_5421_; lean_object* v_res_5422_; 
v_flag_boxed_5421_ = lean_unbox(v_flag_5420_);
v_res_5422_ = l_Lean_Expr_setPPExplicit(v_e_5419_, v_flag_boxed_5421_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* v_e_5427_, uint8_t v_flag_5428_){
_start:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = ((lean_object*)(l_Lean_Expr_setPPUniverses___closed__1));
v___x_5430_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5427_, v___x_5429_, v_flag_5428_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* v_e_5431_, lean_object* v_flag_5432_){
_start:
{
uint8_t v_flag_boxed_5433_; lean_object* v_res_5434_; 
v_flag_boxed_5433_ = lean_unbox(v_flag_5432_);
v_res_5434_ = l_Lean_Expr_setPPUniverses(v_e_5431_, v_flag_boxed_5433_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes(lean_object* v_e_5439_, uint8_t v_flag_5440_){
_start:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = ((lean_object*)(l_Lean_Expr_setPPPiBinderTypes___closed__1));
v___x_5442_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5439_, v___x_5441_, v_flag_5440_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPPiBinderTypes___boxed(lean_object* v_e_5443_, lean_object* v_flag_5444_){
_start:
{
uint8_t v_flag_boxed_5445_; lean_object* v_res_5446_; 
v_flag_boxed_5445_ = lean_unbox(v_flag_5444_);
v_res_5446_ = l_Lean_Expr_setPPPiBinderTypes(v_e_5443_, v_flag_boxed_5445_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes(lean_object* v_e_5451_, uint8_t v_flag_5452_){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = ((lean_object*)(l_Lean_Expr_setPPFunBinderTypes___closed__1));
v___x_5454_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5451_, v___x_5453_, v_flag_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPFunBinderTypes___boxed(lean_object* v_e_5455_, lean_object* v_flag_5456_){
_start:
{
uint8_t v_flag_boxed_5457_; lean_object* v_res_5458_; 
v_flag_boxed_5457_ = lean_unbox(v_flag_5456_);
v_res_5458_ = l_Lean_Expr_setPPFunBinderTypes(v_e_5455_, v_flag_boxed_5457_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes(lean_object* v_e_5463_, uint8_t v_flag_5464_){
_start:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5465_ = ((lean_object*)(l_Lean_Expr_setPPNumericTypes___closed__1));
v___x_5466_ = l_Lean_Expr_setOption___at___00Lean_Expr_setPPExplicit_spec__0(v_e_5463_, v___x_5465_, v_flag_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPNumericTypes___boxed(lean_object* v_e_5467_, lean_object* v_flag_5468_){
_start:
{
uint8_t v_flag_boxed_5469_; lean_object* v_res_5470_; 
v_flag_boxed_5469_ = lean_unbox(v_flag_5468_);
v_res_5470_ = l_Lean_Expr_setPPNumericTypes(v_e_5467_, v_flag_boxed_5469_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(size_t v_sz_5471_, size_t v_i_5472_, lean_object* v_bs_5473_){
_start:
{
uint8_t v___x_5474_; 
v___x_5474_ = lean_usize_dec_lt(v_i_5472_, v_sz_5471_);
if (v___x_5474_ == 0)
{
return v_bs_5473_;
}
else
{
uint8_t v___x_5475_; lean_object* v_v_5476_; lean_object* v___x_5477_; lean_object* v_bs_x27_5478_; lean_object* v___x_5479_; size_t v___x_5480_; size_t v___x_5481_; lean_object* v___x_5482_; 
v___x_5475_ = 0;
v_v_5476_ = lean_array_uget(v_bs_5473_, v_i_5472_);
v___x_5477_ = lean_unsigned_to_nat(0u);
v_bs_x27_5478_ = lean_array_uset(v_bs_5473_, v_i_5472_, v___x_5477_);
v___x_5479_ = l_Lean_Expr_setPPExplicit(v_v_5476_, v___x_5475_);
v___x_5480_ = ((size_t)1ULL);
v___x_5481_ = lean_usize_add(v_i_5472_, v___x_5480_);
v___x_5482_ = lean_array_uset(v_bs_x27_5478_, v_i_5472_, v___x_5479_);
v_i_5472_ = v___x_5481_;
v_bs_5473_ = v___x_5482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0___boxed(lean_object* v_sz_5484_, lean_object* v_i_5485_, lean_object* v_bs_5486_){
_start:
{
size_t v_sz_boxed_5487_; size_t v_i_boxed_5488_; lean_object* v_res_5489_; 
v_sz_boxed_5487_ = lean_unbox_usize(v_sz_5484_);
lean_dec(v_sz_5484_);
v_i_boxed_5488_ = lean_unbox_usize(v_i_5485_);
lean_dec(v_i_5485_);
v_res_5489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_boxed_5487_, v_i_boxed_5488_, v_bs_5486_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* v_e_5490_){
_start:
{
if (lean_obj_tag(v_e_5490_) == 5)
{
lean_object* v___x_5491_; uint8_t v___x_5492_; lean_object* v_f_5493_; lean_object* v_dummy_5494_; lean_object* v_nargs_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; size_t v_sz_5500_; size_t v___x_5501_; lean_object* v_args_5502_; lean_object* v___x_5503_; uint8_t v___x_5504_; lean_object* v___x_5505_; 
v___x_5491_ = l_Lean_Expr_getAppFn(v_e_5490_);
v___x_5492_ = 0;
v_f_5493_ = l_Lean_Expr_setPPExplicit(v___x_5491_, v___x_5492_);
v_dummy_5494_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5495_ = l_Lean_Expr_getAppNumArgs(v_e_5490_);
lean_inc(v_nargs_5495_);
v___x_5496_ = lean_mk_array(v_nargs_5495_, v_dummy_5494_);
v___x_5497_ = lean_unsigned_to_nat(1u);
v___x_5498_ = lean_nat_sub(v_nargs_5495_, v___x_5497_);
lean_dec(v_nargs_5495_);
v___x_5499_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5490_, v___x_5496_, v___x_5498_);
v_sz_5500_ = lean_array_size(v___x_5499_);
v___x_5501_ = ((size_t)0ULL);
v_args_5502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicit_spec__0(v_sz_5500_, v___x_5501_, v___x_5499_);
v___x_5503_ = l_Lean_mkAppN(v_f_5493_, v_args_5502_);
lean_dec_ref(v_args_5502_);
v___x_5504_ = 1;
v___x_5505_ = l_Lean_Expr_setPPExplicit(v___x_5503_, v___x_5504_);
return v___x_5505_;
}
else
{
return v_e_5490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(size_t v_sz_5506_, size_t v_i_5507_, lean_object* v_bs_5508_){
_start:
{
uint8_t v___x_5509_; 
v___x_5509_ = lean_usize_dec_lt(v_i_5507_, v_sz_5506_);
if (v___x_5509_ == 0)
{
return v_bs_5508_;
}
else
{
lean_object* v_v_5510_; lean_object* v___x_5511_; lean_object* v_bs_x27_5512_; lean_object* v___y_5514_; uint8_t v___x_5519_; 
v_v_5510_ = lean_array_uget(v_bs_5508_, v_i_5507_);
v___x_5511_ = lean_unsigned_to_nat(0u);
v_bs_x27_5512_ = lean_array_uset(v_bs_5508_, v_i_5507_, v___x_5511_);
v___x_5519_ = l_Lean_Expr_hasMVar(v_v_5510_);
if (v___x_5519_ == 0)
{
lean_object* v___x_5520_; 
v___x_5520_ = l_Lean_Expr_setPPExplicit(v_v_5510_, v___x_5519_);
v___y_5514_ = v___x_5520_;
goto v___jp_5513_;
}
else
{
v___y_5514_ = v_v_5510_;
goto v___jp_5513_;
}
v___jp_5513_:
{
size_t v___x_5515_; size_t v___x_5516_; lean_object* v___x_5517_; 
v___x_5515_ = ((size_t)1ULL);
v___x_5516_ = lean_usize_add(v_i_5507_, v___x_5515_);
v___x_5517_ = lean_array_uset(v_bs_x27_5512_, v_i_5507_, v___y_5514_);
v_i_5507_ = v___x_5516_;
v_bs_5508_ = v___x_5517_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0___boxed(lean_object* v_sz_5521_, lean_object* v_i_5522_, lean_object* v_bs_5523_){
_start:
{
size_t v_sz_boxed_5524_; size_t v_i_boxed_5525_; lean_object* v_res_5526_; 
v_sz_boxed_5524_ = lean_unbox_usize(v_sz_5521_);
lean_dec(v_sz_5521_);
v_i_boxed_5525_ = lean_unbox_usize(v_i_5522_);
lean_dec(v_i_5522_);
v_res_5526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_boxed_5524_, v_i_boxed_5525_, v_bs_5523_);
return v_res_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* v_e_5527_){
_start:
{
if (lean_obj_tag(v_e_5527_) == 5)
{
lean_object* v___x_5528_; uint8_t v___x_5529_; lean_object* v_f_5530_; lean_object* v_dummy_5531_; lean_object* v_nargs_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; size_t v_sz_5537_; size_t v___x_5538_; lean_object* v_args_5539_; lean_object* v___x_5540_; uint8_t v___x_5541_; lean_object* v___x_5542_; 
v___x_5528_ = l_Lean_Expr_getAppFn(v_e_5527_);
v___x_5529_ = 0;
v_f_5530_ = l_Lean_Expr_setPPExplicit(v___x_5528_, v___x_5529_);
v_dummy_5531_ = lean_obj_once(&l_Lean_Expr_getAppArgs___closed__0, &l_Lean_Expr_getAppArgs___closed__0_once, _init_l_Lean_Expr_getAppArgs___closed__0);
v_nargs_5532_ = l_Lean_Expr_getAppNumArgs(v_e_5527_);
lean_inc(v_nargs_5532_);
v___x_5533_ = lean_mk_array(v_nargs_5532_, v_dummy_5531_);
v___x_5534_ = lean_unsigned_to_nat(1u);
v___x_5535_ = lean_nat_sub(v_nargs_5532_, v___x_5534_);
lean_dec(v_nargs_5532_);
v___x_5536_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_5527_, v___x_5533_, v___x_5535_);
v_sz_5537_ = lean_array_size(v___x_5536_);
v___x_5538_ = ((size_t)0ULL);
v_args_5539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Expr_setAppPPExplicitForExposingMVars_spec__0(v_sz_5537_, v___x_5538_, v___x_5536_);
v___x_5540_ = l_Lean_mkAppN(v_f_5530_, v_args_5539_);
lean_dec_ref(v_args_5539_);
v___x_5541_ = 1;
v___x_5542_ = l_Lean_Expr_setPPExplicit(v___x_5540_, v___x_5541_);
return v___x_5542_;
}
else
{
return v_e_5527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__0(lean_object* v_f_5543_, lean_object* v_body_5544_, lean_object* v_x_5545_){
_start:
{
lean_object* v___x_5546_; 
v___x_5546_ = lean_apply_1(v_f_5543_, v_body_5544_);
return v___x_5546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__1(lean_object* v_f_5547_, lean_object* v_binderType_5548_, lean_object* v_x_5549_){
_start:
{
lean_object* v___x_5550_; 
v___x_5550_ = lean_apply_1(v_f_5547_, v_binderType_5548_);
return v___x_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__5(lean_object* v_f_5551_, lean_object* v_value_5552_, lean_object* v_x_5553_){
_start:
{
lean_object* v___x_5554_; 
v___x_5554_ = lean_apply_1(v_f_5551_, v_value_5552_);
return v___x_5554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__2(lean_object* v_f_5555_, lean_object* v_type_5556_, lean_object* v_x_5557_){
_start:
{
lean_object* v___x_5558_; 
v___x_5558_ = lean_apply_1(v_f_5555_, v_type_5556_);
return v___x_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__3(lean_object* v_f_5559_, lean_object* v_arg_5560_, lean_object* v_x_5561_){
_start:
{
lean_object* v___x_5562_; 
v___x_5562_ = lean_apply_1(v_f_5559_, v_arg_5560_);
return v___x_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg___lam__4(lean_object* v_f_5563_, lean_object* v_fn_5564_, lean_object* v_x_5565_){
_start:
{
lean_object* v___x_5566_; 
v___x_5566_ = lean_apply_1(v_f_5563_, v_fn_5564_);
return v___x_5566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___redArg(lean_object* v_inst_5567_, lean_object* v_f_5568_, lean_object* v_x_5569_){
_start:
{
switch(lean_obj_tag(v_x_5569_))
{
case 7:
{
lean_object* v_toPure_5570_; lean_object* v_toSeq_5571_; lean_object* v_binderType_5572_; lean_object* v_body_5573_; lean_object* v___f_5574_; lean_object* v___f_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v_toPure_5570_ = lean_ctor_get(v_inst_5567_, 1);
lean_inc(v_toPure_5570_);
v_toSeq_5571_ = lean_ctor_get(v_inst_5567_, 2);
lean_inc_n(v_toSeq_5571_, 2);
lean_dec_ref(v_inst_5567_);
v_binderType_5572_ = lean_ctor_get(v_x_5569_, 1);
v_body_5573_ = lean_ctor_get(v_x_5569_, 2);
lean_inc_ref(v_body_5573_);
lean_inc(v_f_5568_);
v___f_5574_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5574_, 0, v_f_5568_);
lean_closure_set(v___f_5574_, 1, v_body_5573_);
lean_inc_ref(v_binderType_5572_);
v___f_5575_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5575_, 0, v_f_5568_);
lean_closure_set(v___f_5575_, 1, v_binderType_5572_);
v___x_5576_ = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21), 3, 1);
lean_closure_set(v___x_5576_, 0, v_x_5569_);
v___x_5577_ = lean_apply_2(v_toPure_5570_, lean_box(0), v___x_5576_);
v___x_5578_ = lean_apply_4(v_toSeq_5571_, lean_box(0), lean_box(0), v___x_5577_, v___f_5575_);
v___x_5579_ = lean_apply_4(v_toSeq_5571_, lean_box(0), lean_box(0), v___x_5578_, v___f_5574_);
return v___x_5579_;
}
case 6:
{
lean_object* v_toPure_5580_; lean_object* v_toSeq_5581_; lean_object* v_binderType_5582_; lean_object* v_body_5583_; lean_object* v___f_5584_; lean_object* v___f_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_toPure_5580_ = lean_ctor_get(v_inst_5567_, 1);
lean_inc(v_toPure_5580_);
v_toSeq_5581_ = lean_ctor_get(v_inst_5567_, 2);
lean_inc_n(v_toSeq_5581_, 2);
lean_dec_ref(v_inst_5567_);
v_binderType_5582_ = lean_ctor_get(v_x_5569_, 1);
v_body_5583_ = lean_ctor_get(v_x_5569_, 2);
lean_inc_ref(v_body_5583_);
lean_inc(v_f_5568_);
v___f_5584_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5584_, 0, v_f_5568_);
lean_closure_set(v___f_5584_, 1, v_body_5583_);
lean_inc_ref(v_binderType_5582_);
v___f_5585_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5585_, 0, v_f_5568_);
lean_closure_set(v___f_5585_, 1, v_binderType_5582_);
v___x_5586_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21), 3, 1);
lean_closure_set(v___x_5586_, 0, v_x_5569_);
v___x_5587_ = lean_apply_2(v_toPure_5580_, lean_box(0), v___x_5586_);
v___x_5588_ = lean_apply_4(v_toSeq_5581_, lean_box(0), lean_box(0), v___x_5587_, v___f_5585_);
v___x_5589_ = lean_apply_4(v_toSeq_5581_, lean_box(0), lean_box(0), v___x_5588_, v___f_5584_);
return v___x_5589_;
}
case 10:
{
lean_object* v_toFunctor_5590_; lean_object* v_expr_5591_; lean_object* v_map_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; 
v_toFunctor_5590_ = lean_ctor_get(v_inst_5567_, 0);
lean_inc_ref(v_toFunctor_5590_);
lean_dec_ref(v_inst_5567_);
v_expr_5591_ = lean_ctor_get(v_x_5569_, 1);
lean_inc_ref(v_expr_5591_);
v_map_5592_ = lean_ctor_get(v_toFunctor_5590_, 0);
lean_inc(v_map_5592_);
lean_dec_ref(v_toFunctor_5590_);
v___x_5593_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_5593_, 0, v_x_5569_);
v___x_5594_ = lean_apply_1(v_f_5568_, v_expr_5591_);
v___x_5595_ = lean_apply_4(v_map_5592_, lean_box(0), lean_box(0), v___x_5593_, v___x_5594_);
return v___x_5595_;
}
case 8:
{
lean_object* v_toPure_5596_; lean_object* v_toSeq_5597_; lean_object* v_type_5598_; lean_object* v_value_5599_; lean_object* v_body_5600_; lean_object* v___f_5601_; lean_object* v___f_5602_; lean_object* v___f_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
v_toPure_5596_ = lean_ctor_get(v_inst_5567_, 1);
lean_inc(v_toPure_5596_);
v_toSeq_5597_ = lean_ctor_get(v_inst_5567_, 2);
lean_inc_n(v_toSeq_5597_, 3);
lean_dec_ref(v_inst_5567_);
v_type_5598_ = lean_ctor_get(v_x_5569_, 1);
v_value_5599_ = lean_ctor_get(v_x_5569_, 2);
v_body_5600_ = lean_ctor_get(v_x_5569_, 3);
lean_inc_ref(v_body_5600_);
lean_inc_n(v_f_5568_, 2);
v___f_5601_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5601_, 0, v_f_5568_);
lean_closure_set(v___f_5601_, 1, v_body_5600_);
lean_inc_ref(v_value_5599_);
v___f_5602_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__5), 3, 2);
lean_closure_set(v___f_5602_, 0, v_f_5568_);
lean_closure_set(v___f_5602_, 1, v_value_5599_);
lean_inc_ref(v_type_5598_);
v___f_5603_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__2), 3, 2);
lean_closure_set(v___f_5603_, 0, v_f_5568_);
lean_closure_set(v___f_5603_, 1, v_type_5598_);
v___x_5604_ = lean_alloc_closure((void*)(l_Lean_Expr_updateLetE_x21), 4, 1);
lean_closure_set(v___x_5604_, 0, v_x_5569_);
v___x_5605_ = lean_apply_2(v_toPure_5596_, lean_box(0), v___x_5604_);
v___x_5606_ = lean_apply_4(v_toSeq_5597_, lean_box(0), lean_box(0), v___x_5605_, v___f_5603_);
v___x_5607_ = lean_apply_4(v_toSeq_5597_, lean_box(0), lean_box(0), v___x_5606_, v___f_5602_);
v___x_5608_ = lean_apply_4(v_toSeq_5597_, lean_box(0), lean_box(0), v___x_5607_, v___f_5601_);
return v___x_5608_;
}
case 5:
{
lean_object* v_toPure_5609_; lean_object* v_toSeq_5610_; lean_object* v_fn_5611_; lean_object* v_arg_5612_; lean_object* v___f_5613_; lean_object* v___f_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v_toPure_5609_ = lean_ctor_get(v_inst_5567_, 1);
lean_inc(v_toPure_5609_);
v_toSeq_5610_ = lean_ctor_get(v_inst_5567_, 2);
lean_inc_n(v_toSeq_5610_, 2);
lean_dec_ref(v_inst_5567_);
v_fn_5611_ = lean_ctor_get(v_x_5569_, 0);
v_arg_5612_ = lean_ctor_get(v_x_5569_, 1);
lean_inc_ref(v_arg_5612_);
lean_inc(v_f_5568_);
v___f_5613_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__3), 3, 2);
lean_closure_set(v___f_5613_, 0, v_f_5568_);
lean_closure_set(v___f_5613_, 1, v_arg_5612_);
lean_inc_ref(v_fn_5611_);
v___f_5614_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___redArg___lam__4), 3, 2);
lean_closure_set(v___f_5614_, 0, v_f_5568_);
lean_closure_set(v___f_5614_, 1, v_fn_5611_);
v___x_5615_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_5615_, 0, v_x_5569_);
v___x_5616_ = lean_apply_2(v_toPure_5609_, lean_box(0), v___x_5615_);
v___x_5617_ = lean_apply_4(v_toSeq_5610_, lean_box(0), lean_box(0), v___x_5616_, v___f_5614_);
v___x_5618_ = lean_apply_4(v_toSeq_5610_, lean_box(0), lean_box(0), v___x_5617_, v___f_5613_);
return v___x_5618_;
}
case 11:
{
lean_object* v_toFunctor_5619_; lean_object* v_struct_5620_; lean_object* v_map_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v_toFunctor_5619_ = lean_ctor_get(v_inst_5567_, 0);
lean_inc_ref(v_toFunctor_5619_);
lean_dec_ref(v_inst_5567_);
v_struct_5620_ = lean_ctor_get(v_x_5569_, 2);
lean_inc_ref(v_struct_5620_);
v_map_5621_ = lean_ctor_get(v_toFunctor_5619_, 0);
lean_inc(v_map_5621_);
lean_dec_ref(v_toFunctor_5619_);
v___x_5622_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_5622_, 0, v_x_5569_);
v___x_5623_ = lean_apply_1(v_f_5568_, v_struct_5620_);
v___x_5624_ = lean_apply_4(v_map_5621_, lean_box(0), lean_box(0), v___x_5622_, v___x_5623_);
return v___x_5624_;
}
default: 
{
lean_object* v_toPure_5625_; lean_object* v___x_5626_; 
lean_dec(v_f_5568_);
v_toPure_5625_ = lean_ctor_get(v_inst_5567_, 1);
lean_inc(v_toPure_5625_);
lean_dec_ref(v_inst_5567_);
v___x_5626_ = lean_apply_2(v_toPure_5625_, lean_box(0), v_x_5569_);
return v___x_5626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren(lean_object* v_M_5627_, lean_object* v_inst_5628_, lean_object* v_f_5629_, lean_object* v_x_5630_){
_start:
{
lean_object* v___x_5631_; 
v___x_5631_ = l_Lean_Expr_traverseChildren___redArg(v_inst_5628_, v_f_5629_, v_x_5630_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0(lean_object* v_self_5632_){
_start:
{
lean_object* v_snd_5633_; 
v_snd_5633_ = lean_ctor_get(v_self_5632_, 1);
lean_inc(v_snd_5633_);
return v_snd_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__0___boxed(lean_object* v_self_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l_Lean_Expr_foldlM___redArg___lam__0(v_self_5634_);
lean_dec_ref(v_self_5634_);
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__1(lean_object* v_e_x27_5636_, lean_object* v_snd_5637_){
_start:
{
lean_object* v___x_5638_; 
v___x_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5638_, 0, v_e_x27_5636_);
lean_ctor_set(v___x_5638_, 1, v_snd_5637_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg___lam__2(lean_object* v_f_5639_, lean_object* v_map_5640_, lean_object* v_e_x27_5641_, lean_object* v_a_5642_){
_start:
{
lean_object* v___f_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
lean_inc_ref(v_e_x27_5641_);
v___f_5643_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_5643_, 0, v_e_x27_5641_);
v___x_5644_ = lean_apply_2(v_f_5639_, v_a_5642_, v_e_x27_5641_);
v___x_5645_ = lean_apply_4(v_map_5640_, lean_box(0), lean_box(0), v___f_5643_, v___x_5644_);
return v___x_5645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___redArg(lean_object* v_inst_5647_, lean_object* v_f_5648_, lean_object* v_init_5649_, lean_object* v_e_5650_){
_start:
{
lean_object* v_toApplicative_5651_; lean_object* v_toFunctor_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5679_; 
v_toApplicative_5651_ = lean_ctor_get(v_inst_5647_, 0);
lean_inc_ref(v_toApplicative_5651_);
v_toFunctor_5652_ = lean_ctor_get(v_toApplicative_5651_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v_toApplicative_5651_);
if (v_isSharedCheck_5679_ == 0)
{
lean_object* v_unused_5680_; lean_object* v_unused_5681_; lean_object* v_unused_5682_; lean_object* v_unused_5683_; 
v_unused_5680_ = lean_ctor_get(v_toApplicative_5651_, 4);
lean_dec(v_unused_5680_);
v_unused_5681_ = lean_ctor_get(v_toApplicative_5651_, 3);
lean_dec(v_unused_5681_);
v_unused_5682_ = lean_ctor_get(v_toApplicative_5651_, 2);
lean_dec(v_unused_5682_);
v_unused_5683_ = lean_ctor_get(v_toApplicative_5651_, 1);
lean_dec(v_unused_5683_);
v___x_5654_ = v_toApplicative_5651_;
v_isShared_5655_ = v_isSharedCheck_5679_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_toFunctor_5652_);
lean_dec(v_toApplicative_5651_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5679_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v_map_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5677_; 
v_map_5656_ = lean_ctor_get(v_toFunctor_5652_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_toFunctor_5652_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; 
v_unused_5678_ = lean_ctor_get(v_toFunctor_5652_, 1);
lean_dec(v_unused_5678_);
v___x_5658_ = v_toFunctor_5652_;
v_isShared_5659_ = v_isSharedCheck_5677_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_map_5656_);
lean_dec(v_toFunctor_5652_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5677_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___f_5660_; lean_object* v___f_5661_; lean_object* v___f_5662_; lean_object* v___f_5663_; lean_object* v___f_5664_; lean_object* v___f_5665_; lean_object* v___x_5666_; lean_object* v___x_5668_; 
v___f_5660_ = ((lean_object*)(l_Lean_Expr_foldlM___redArg___closed__0));
lean_inc(v_map_5656_);
v___f_5661_ = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_5661_, 0, v_f_5648_);
lean_closure_set(v___f_5661_, 1, v_map_5656_);
lean_inc_ref_n(v_inst_5647_, 5);
v___f_5662_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5662_, 0, v_inst_5647_);
v___f_5663_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5663_, 0, v_inst_5647_);
v___f_5664_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_5664_, 0, v_inst_5647_);
v___f_5665_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_5665_, 0, v_inst_5647_);
v___x_5666_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_5666_, 0, lean_box(0));
lean_closure_set(v___x_5666_, 1, lean_box(0));
lean_closure_set(v___x_5666_, 2, v_inst_5647_);
if (v_isShared_5659_ == 0)
{
lean_ctor_set(v___x_5658_, 1, v___f_5662_);
lean_ctor_set(v___x_5658_, 0, v___x_5666_);
v___x_5668_ = v___x_5658_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5666_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v___f_5662_);
v___x_5668_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
lean_object* v___x_5669_; lean_object* v___x_5671_; 
v___x_5669_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_5669_, 0, lean_box(0));
lean_closure_set(v___x_5669_, 1, lean_box(0));
lean_closure_set(v___x_5669_, 2, v_inst_5647_);
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 4, v___f_5665_);
lean_ctor_set(v___x_5654_, 3, v___f_5664_);
lean_ctor_set(v___x_5654_, 2, v___f_5663_);
lean_ctor_set(v___x_5654_, 1, v___x_5669_);
lean_ctor_set(v___x_5654_, 0, v___x_5668_);
v___x_5671_ = v___x_5654_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5668_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v___x_5669_);
lean_ctor_set(v_reuseFailAlloc_5675_, 2, v___f_5663_);
lean_ctor_set(v_reuseFailAlloc_5675_, 3, v___f_5664_);
lean_ctor_set(v_reuseFailAlloc_5675_, 4, v___f_5665_);
v___x_5671_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
lean_object* v___x_30__overap_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_30__overap_5672_ = l_Lean_Expr_traverseChildren___redArg(v___x_5671_, v___f_5661_, v_e_5650_);
v___x_5673_ = lean_apply_1(v___x_30__overap_5672_, v_init_5649_);
v___x_5674_ = lean_apply_4(v_map_5656_, lean_box(0), lean_box(0), v___f_5660_, v___x_5673_);
return v___x_5674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM(lean_object* v_00_u03b1_5684_, lean_object* v_m_5685_, lean_object* v_inst_5686_, lean_object* v_f_5687_, lean_object* v_init_5688_, lean_object* v_e_5689_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l_Lean_Expr_foldlM___redArg(v_inst_5686_, v_f_5687_, v_init_5688_, v_e_5689_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object* v_x_5691_){
_start:
{
lean_object* v_d_5693_; lean_object* v_b_5694_; 
switch(lean_obj_tag(v_x_5691_))
{
case 5:
{
lean_object* v_fn_5700_; lean_object* v_arg_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v_fn_5700_ = lean_ctor_get(v_x_5691_, 0);
v_arg_5701_ = lean_ctor_get(v_x_5691_, 1);
v___x_5702_ = lean_unsigned_to_nat(1u);
v___x_5703_ = l_Lean_Expr_sizeWithoutSharing(v_fn_5700_);
v___x_5704_ = lean_nat_add(v___x_5702_, v___x_5703_);
lean_dec(v___x_5703_);
v___x_5705_ = l_Lean_Expr_sizeWithoutSharing(v_arg_5701_);
v___x_5706_ = lean_nat_add(v___x_5704_, v___x_5705_);
lean_dec(v___x_5705_);
lean_dec(v___x_5704_);
return v___x_5706_;
}
case 6:
{
lean_object* v_binderType_5707_; lean_object* v_body_5708_; 
v_binderType_5707_ = lean_ctor_get(v_x_5691_, 1);
v_body_5708_ = lean_ctor_get(v_x_5691_, 2);
v_d_5693_ = v_binderType_5707_;
v_b_5694_ = v_body_5708_;
goto v___jp_5692_;
}
case 7:
{
lean_object* v_binderType_5709_; lean_object* v_body_5710_; 
v_binderType_5709_ = lean_ctor_get(v_x_5691_, 1);
v_body_5710_ = lean_ctor_get(v_x_5691_, 2);
v_d_5693_ = v_binderType_5709_;
v_b_5694_ = v_body_5710_;
goto v___jp_5692_;
}
case 8:
{
lean_object* v_type_5711_; lean_object* v_value_5712_; lean_object* v_body_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; 
v_type_5711_ = lean_ctor_get(v_x_5691_, 1);
v_value_5712_ = lean_ctor_get(v_x_5691_, 2);
v_body_5713_ = lean_ctor_get(v_x_5691_, 3);
v___x_5714_ = lean_unsigned_to_nat(1u);
v___x_5715_ = l_Lean_Expr_sizeWithoutSharing(v_type_5711_);
v___x_5716_ = lean_nat_add(v___x_5714_, v___x_5715_);
lean_dec(v___x_5715_);
v___x_5717_ = l_Lean_Expr_sizeWithoutSharing(v_value_5712_);
v___x_5718_ = lean_nat_add(v___x_5716_, v___x_5717_);
lean_dec(v___x_5717_);
lean_dec(v___x_5716_);
v___x_5719_ = l_Lean_Expr_sizeWithoutSharing(v_body_5713_);
v___x_5720_ = lean_nat_add(v___x_5718_, v___x_5719_);
lean_dec(v___x_5719_);
lean_dec(v___x_5718_);
return v___x_5720_;
}
case 10:
{
lean_object* v_expr_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; 
v_expr_5721_ = lean_ctor_get(v_x_5691_, 1);
v___x_5722_ = lean_unsigned_to_nat(1u);
v___x_5723_ = l_Lean_Expr_sizeWithoutSharing(v_expr_5721_);
v___x_5724_ = lean_nat_add(v___x_5722_, v___x_5723_);
lean_dec(v___x_5723_);
return v___x_5724_;
}
case 11:
{
lean_object* v_struct_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; 
v_struct_5725_ = lean_ctor_get(v_x_5691_, 2);
v___x_5726_ = lean_unsigned_to_nat(1u);
v___x_5727_ = l_Lean_Expr_sizeWithoutSharing(v_struct_5725_);
v___x_5728_ = lean_nat_add(v___x_5726_, v___x_5727_);
lean_dec(v___x_5727_);
return v___x_5728_;
}
default: 
{
lean_object* v___x_5729_; 
v___x_5729_ = lean_unsigned_to_nat(1u);
return v___x_5729_;
}
}
v___jp_5692_:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5695_ = lean_unsigned_to_nat(1u);
v___x_5696_ = l_Lean_Expr_sizeWithoutSharing(v_d_5693_);
v___x_5697_ = lean_nat_add(v___x_5695_, v___x_5696_);
lean_dec(v___x_5696_);
v___x_5698_ = l_Lean_Expr_sizeWithoutSharing(v_b_5694_);
v___x_5699_ = lean_nat_add(v___x_5697_, v___x_5698_);
lean_dec(v___x_5698_);
lean_dec(v___x_5697_);
return v___x_5699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sizeWithoutSharing___boxed(lean_object* v_x_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l_Lean_Expr_sizeWithoutSharing(v_x_5730_);
lean_dec_ref(v_x_5730_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* v_kind_5734_, lean_object* v_e_5735_){
_start:
{
lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5736_ = l_Lean_KVMap_empty;
v___x_5737_ = ((lean_object*)(l_Lean_mkAnnotation___closed__0));
v___x_5738_ = l_Lean_KVMap_insert(v___x_5736_, v_kind_5734_, v___x_5737_);
v___x_5739_ = l_Lean_Expr_mdata___override(v___x_5738_, v_e_5735_);
return v___x_5739_;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* v_kind_5740_, lean_object* v_e_5741_){
_start:
{
if (lean_obj_tag(v_e_5741_) == 10)
{
lean_object* v_data_5742_; lean_object* v_expr_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; uint8_t v___x_5746_; 
v_data_5742_ = lean_ctor_get(v_e_5741_, 0);
v_expr_5743_ = lean_ctor_get(v_e_5741_, 1);
v___x_5744_ = l_Lean_KVMap_size(v_data_5742_);
v___x_5745_ = lean_unsigned_to_nat(1u);
v___x_5746_ = lean_nat_dec_eq(v___x_5744_, v___x_5745_);
lean_dec(v___x_5744_);
if (v___x_5746_ == 0)
{
lean_object* v___x_5747_; 
v___x_5747_ = lean_box(0);
return v___x_5747_;
}
else
{
uint8_t v___x_5748_; uint8_t v___x_5749_; 
v___x_5748_ = 0;
v___x_5749_ = l_Lean_KVMap_getBool(v_data_5742_, v_kind_5740_, v___x_5748_);
if (v___x_5749_ == 0)
{
lean_object* v___x_5750_; 
v___x_5750_ = lean_box(0);
return v___x_5750_;
}
else
{
lean_object* v___x_5751_; 
lean_inc_ref(v_expr_5743_);
v___x_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5751_, 0, v_expr_5743_);
return v___x_5751_;
}
}
}
else
{
lean_object* v___x_5752_; 
v___x_5752_ = lean_box(0);
return v___x_5752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* v_kind_5753_, lean_object* v_e_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lean_annotation_x3f(v_kind_5753_, v_e_5754_);
lean_dec_ref(v_e_5754_);
lean_dec(v_kind_5753_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* v_e_5759_){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; 
v___x_5760_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5761_ = l_Lean_mkAnnotation(v___x_5760_, v_e_5759_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* v_e_5762_){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = ((lean_object*)(l_Lean_mkInaccessible___closed__1));
v___x_5764_ = l_Lean_annotation_x3f(v___x_5763_, v_e_5762_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* v_e_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l_Lean_inaccessible_x3f(v_e_5765_);
lean_dec_ref(v_e_5765_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* v_p_5771_){
_start:
{
if (lean_obj_tag(v_p_5771_) == 10)
{
lean_object* v_data_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v_data_5772_ = lean_ctor_get(v_p_5771_, 0);
v___x_5773_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5774_ = l_Lean_KVMap_find(v_data_5772_, v___x_5773_);
if (lean_obj_tag(v___x_5774_) == 1)
{
lean_object* v_val_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5786_; 
v_val_5775_ = lean_ctor_get(v___x_5774_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5774_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5777_ = v___x_5774_;
v_isShared_5778_ = v_isSharedCheck_5786_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_val_5775_);
lean_dec(v___x_5774_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5786_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
if (lean_obj_tag(v_val_5775_) == 5)
{
lean_object* v_v_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5783_; 
v_v_5779_ = lean_ctor_get(v_val_5775_, 0);
lean_inc(v_v_5779_);
lean_dec_ref_known(v_val_5775_, 1);
v___x_5780_ = l_Lean_Expr_mdataExpr_x21(v_p_5771_);
v___x_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5781_, 0, v_v_5779_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 0, v___x_5781_);
v___x_5783_ = v___x_5777_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5781_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
else
{
lean_object* v___x_5785_; 
lean_del_object(v___x_5777_);
lean_dec(v_val_5775_);
v___x_5785_ = lean_box(0);
return v___x_5785_;
}
}
}
else
{
lean_object* v___x_5787_; 
lean_dec(v___x_5774_);
v___x_5787_ = lean_box(0);
return v___x_5787_;
}
}
else
{
lean_object* v___x_5788_; 
v___x_5788_ = lean_box(0);
return v___x_5788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* v_p_5789_){
_start:
{
lean_object* v_res_5790_; 
v_res_5790_ = l_Lean_patternWithRef_x3f(v_p_5789_);
lean_dec_ref(v_p_5789_);
return v_res_5790_;
}
}
LEAN_EXPORT uint8_t l_Lean_isPatternWithRef(lean_object* v_p_5791_){
_start:
{
lean_object* v___x_5792_; 
v___x_5792_ = l_Lean_patternWithRef_x3f(v_p_5791_);
if (lean_obj_tag(v___x_5792_) == 0)
{
uint8_t v___x_5793_; 
v___x_5793_ = 0;
return v___x_5793_;
}
else
{
uint8_t v___x_5794_; 
lean_dec_ref_known(v___x_5792_, 1);
v___x_5794_ = 1;
return v___x_5794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isPatternWithRef___boxed(lean_object* v_p_5795_){
_start:
{
uint8_t v_res_5796_; lean_object* v_r_5797_; 
v_res_5796_ = l_Lean_isPatternWithRef(v_p_5795_);
lean_dec_ref(v_p_5795_);
v_r_5797_ = lean_box(v_res_5796_);
return v_r_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* v_p_5798_, lean_object* v_stx_5799_){
_start:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Lean_patternWithRef_x3f(v_p_5798_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5801_ = l_Lean_KVMap_empty;
v___x_5802_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey));
v___x_5803_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_5803_, 0, v_stx_5799_);
v___x_5804_ = l_Lean_KVMap_insert(v___x_5801_, v___x_5802_, v___x_5803_);
v___x_5805_ = l_Lean_Expr_mdata___override(v___x_5804_, v_p_5798_);
return v___x_5805_;
}
else
{
lean_dec_ref_known(v___x_5800_, 1);
lean_dec(v_stx_5799_);
return v_p_5798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* v_e_5806_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l_Lean_inaccessible_x3f(v_e_5806_);
if (lean_obj_tag(v___x_5807_) == 1)
{
return v___x_5807_;
}
else
{
lean_object* v___x_5808_; 
lean_dec(v___x_5807_);
v___x_5808_ = l_Lean_patternWithRef_x3f(v_e_5806_);
if (lean_obj_tag(v___x_5808_) == 1)
{
lean_object* v_val_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5817_; 
v_val_5809_ = lean_ctor_get(v___x_5808_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5811_ = v___x_5808_;
v_isShared_5812_ = v_isSharedCheck_5817_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_val_5809_);
lean_dec(v___x_5808_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5817_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v_snd_5813_; lean_object* v___x_5815_; 
v_snd_5813_ = lean_ctor_get(v_val_5809_, 1);
lean_inc(v_snd_5813_);
lean_dec(v_val_5809_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 0, v_snd_5813_);
v___x_5815_ = v___x_5811_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_snd_5813_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
else
{
lean_object* v___x_5818_; 
lean_dec(v___x_5808_);
v___x_5818_ = lean_box(0);
return v___x_5818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* v_e_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_Lean_patternAnnotation_x3f(v_e_5819_);
lean_dec_ref(v_e_5819_);
return v_res_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoalRaw(lean_object* v_e_5824_){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5826_ = l_Lean_mkAnnotation(v___x_5825_, v_e_5824_);
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* v_e_5830_){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5831_ = ((lean_object*)(l_Lean_mkLHSGoalRaw___closed__1));
v___x_5832_ = l_Lean_annotation_x3f(v___x_5831_, v_e_5830_);
if (lean_obj_tag(v___x_5832_) == 0)
{
return v___x_5832_;
}
else
{
lean_object* v_val_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5846_; 
v_val_5833_ = lean_ctor_get(v___x_5832_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5832_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5835_ = v___x_5832_;
v_isShared_5836_ = v_isSharedCheck_5846_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_val_5833_);
lean_dec(v___x_5832_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5846_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v___x_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; 
v___x_5837_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_5838_ = lean_unsigned_to_nat(3u);
v___x_5839_ = l_Lean_Expr_isAppOfArity(v_val_5833_, v___x_5837_, v___x_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; 
lean_del_object(v___x_5835_);
lean_dec(v_val_5833_);
v___x_5840_ = lean_box(0);
return v___x_5840_;
}
else
{
lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5844_; 
v___x_5841_ = l_Lean_Expr_appFn_x21(v_val_5833_);
lean_dec(v_val_5833_);
v___x_5842_ = l_Lean_Expr_appArg_x21(v___x_5841_);
lean_dec_ref(v___x_5841_);
if (v_isShared_5836_ == 0)
{
lean_ctor_set(v___x_5835_, 0, v___x_5842_);
v___x_5844_ = v___x_5835_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5842_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* v_e_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_isLHSGoal_x3f(v_e_5847_);
lean_dec_ref(v_e_5847_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg___lam__0(lean_object* v_toPure_5849_, lean_object* v_____do__lift_5850_){
_start:
{
lean_object* v___x_5851_; 
v___x_5851_ = lean_apply_2(v_toPure_5849_, lean_box(0), v_____do__lift_5850_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___redArg(lean_object* v_inst_5852_, lean_object* v_inst_5853_){
_start:
{
lean_object* v_toApplicative_5854_; lean_object* v_toBind_5855_; lean_object* v_toPure_5856_; lean_object* v___x_5857_; lean_object* v___f_5858_; lean_object* v___x_5859_; 
v_toApplicative_5854_ = lean_ctor_get(v_inst_5852_, 0);
v_toBind_5855_ = lean_ctor_get(v_inst_5852_, 1);
lean_inc(v_toBind_5855_);
v_toPure_5856_ = lean_ctor_get(v_toApplicative_5854_, 1);
lean_inc(v_toPure_5856_);
v___x_5857_ = l_Lean_mkFreshId___redArg(v_inst_5852_, v_inst_5853_);
v___f_5858_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5858_, 0, v_toPure_5856_);
v___x_5859_ = lean_apply_4(v_toBind_5855_, lean_box(0), lean_box(0), v___x_5857_, v___f_5858_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* v_m_5860_, lean_object* v_inst_5861_, lean_object* v_inst_5862_){
_start:
{
lean_object* v___x_5863_; 
v___x_5863_ = l_Lean_mkFreshFVarId___redArg(v_inst_5861_, v_inst_5862_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___redArg(lean_object* v_inst_5864_, lean_object* v_inst_5865_){
_start:
{
lean_object* v_toApplicative_5866_; lean_object* v_toBind_5867_; lean_object* v_toPure_5868_; lean_object* v___x_5869_; lean_object* v___f_5870_; lean_object* v___x_5871_; 
v_toApplicative_5866_ = lean_ctor_get(v_inst_5864_, 0);
v_toBind_5867_ = lean_ctor_get(v_inst_5864_, 1);
lean_inc(v_toBind_5867_);
v_toPure_5868_ = lean_ctor_get(v_toApplicative_5866_, 1);
lean_inc(v_toPure_5868_);
v___x_5869_ = l_Lean_mkFreshId___redArg(v_inst_5864_, v_inst_5865_);
v___f_5870_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5870_, 0, v_toPure_5868_);
v___x_5871_ = lean_apply_4(v_toBind_5867_, lean_box(0), lean_box(0), v___x_5869_, v___f_5870_);
return v___x_5871_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* v_m_5872_, lean_object* v_inst_5873_, lean_object* v_inst_5874_){
_start:
{
lean_object* v___x_5875_; 
v___x_5875_ = l_Lean_mkFreshMVarId___redArg(v_inst_5873_, v_inst_5874_);
return v___x_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___redArg(lean_object* v_inst_5876_, lean_object* v_inst_5877_){
_start:
{
lean_object* v_toApplicative_5878_; lean_object* v_toBind_5879_; lean_object* v_toPure_5880_; lean_object* v___x_5881_; lean_object* v___f_5882_; lean_object* v___x_5883_; 
v_toApplicative_5878_ = lean_ctor_get(v_inst_5876_, 0);
v_toBind_5879_ = lean_ctor_get(v_inst_5876_, 1);
lean_inc(v_toBind_5879_);
v_toPure_5880_ = lean_ctor_get(v_toApplicative_5878_, 1);
lean_inc(v_toPure_5880_);
v___x_5881_ = l_Lean_mkFreshId___redArg(v_inst_5876_, v_inst_5877_);
v___f_5882_ = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5882_, 0, v_toPure_5880_);
v___x_5883_ = lean_apply_4(v_toBind_5879_, lean_box(0), lean_box(0), v___x_5881_, v___f_5882_);
return v___x_5883_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* v_m_5884_, lean_object* v_inst_5885_, lean_object* v_inst_5886_){
_start:
{
lean_object* v___x_5887_; 
v___x_5887_ = l_Lean_mkFreshLMVarId___redArg(v_inst_5885_, v_inst_5886_);
return v___x_5887_;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2(void){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5891_ = lean_box(0);
v___x_5892_ = ((lean_object*)(l_Lean_mkNot___closed__1));
v___x_5893_ = l_Lean_Expr_const___override(v___x_5892_, v___x_5891_);
return v___x_5893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* v_p_5894_){
_start:
{
lean_object* v___x_5895_; lean_object* v___x_5896_; 
v___x_5895_ = lean_obj_once(&l_Lean_mkNot___closed__2, &l_Lean_mkNot___closed__2_once, _init_l_Lean_mkNot___closed__2);
v___x_5896_ = l_Lean_Expr_app___override(v___x_5895_, v_p_5894_);
return v___x_5896_;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5900_ = lean_box(0);
v___x_5901_ = ((lean_object*)(l_Lean_mkOr___closed__1));
v___x_5902_ = l_Lean_Expr_const___override(v___x_5901_, v___x_5900_);
return v___x_5902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* v_p_5903_, lean_object* v_q_5904_){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5905_ = lean_obj_once(&l_Lean_mkOr___closed__2, &l_Lean_mkOr___closed__2_once, _init_l_Lean_mkOr___closed__2);
v___x_5906_ = l_Lean_mkAppB(v___x_5905_, v_p_5903_, v_q_5904_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2(void){
_start:
{
lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5910_ = lean_box(0);
v___x_5911_ = ((lean_object*)(l_Lean_mkAnd___closed__1));
v___x_5912_ = l_Lean_Expr_const___override(v___x_5911_, v___x_5910_);
return v___x_5912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* v_p_5913_, lean_object* v_q_5914_){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5915_ = lean_obj_once(&l_Lean_mkAnd___closed__2, &l_Lean_mkAnd___closed__2_once, _init_l_Lean_mkAnd___closed__2);
v___x_5916_ = l_Lean_mkAppB(v___x_5915_, v_p_5913_, v_q_5914_);
return v___x_5916_;
}
}
static lean_object* _init_l_Lean_mkAndN___closed__0(void){
_start:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5917_ = lean_box(0);
v___x_5918_ = ((lean_object*)(l_Lean_Expr_isTrue___closed__1));
v___x_5919_ = l_Lean_Expr_const___override(v___x_5918_, v___x_5917_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAndN(lean_object* v_x_5920_){
_start:
{
if (lean_obj_tag(v_x_5920_) == 0)
{
lean_object* v___x_5921_; 
v___x_5921_ = lean_obj_once(&l_Lean_mkAndN___closed__0, &l_Lean_mkAndN___closed__0_once, _init_l_Lean_mkAndN___closed__0);
return v___x_5921_;
}
else
{
lean_object* v_tail_5922_; 
v_tail_5922_ = lean_ctor_get(v_x_5920_, 1);
if (lean_obj_tag(v_tail_5922_) == 0)
{
lean_object* v_head_5923_; 
v_head_5923_ = lean_ctor_get(v_x_5920_, 0);
lean_inc(v_head_5923_);
lean_dec_ref_known(v_x_5920_, 2);
return v_head_5923_;
}
else
{
lean_object* v_head_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
lean_inc(v_tail_5922_);
v_head_5924_ = lean_ctor_get(v_x_5920_, 0);
lean_inc(v_head_5924_);
lean_dec_ref_known(v_x_5920_, 2);
v___x_5925_ = l_Lean_mkAndN(v_tail_5922_);
v___x_5926_ = l_Lean_mkAnd(v_head_5924_, v___x_5925_);
return v___x_5926_;
}
}
}
}
static lean_object* _init_l_Lean_mkEM___closed__3(void){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5932_ = lean_box(0);
v___x_5933_ = ((lean_object*)(l_Lean_mkEM___closed__2));
v___x_5934_ = l_Lean_Expr_const___override(v___x_5933_, v___x_5932_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* v_p_5935_){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; 
v___x_5936_ = lean_obj_once(&l_Lean_mkEM___closed__3, &l_Lean_mkEM___closed__3_once, _init_l_Lean_mkEM___closed__3);
v___x_5937_ = l_Lean_Expr_app___override(v___x_5936_, v_p_5935_);
return v___x_5937_;
}
}
static lean_object* _init_l_Lean_mkIff___closed__2(void){
_start:
{
lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; 
v___x_5941_ = lean_box(0);
v___x_5942_ = ((lean_object*)(l_Lean_mkIff___closed__1));
v___x_5943_ = l_Lean_Expr_const___override(v___x_5942_, v___x_5941_);
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIff(lean_object* v_p_5944_, lean_object* v_q_5945_){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; 
v___x_5946_ = lean_obj_once(&l_Lean_mkIff___closed__2, &l_Lean_mkIff___closed__2_once, _init_l_Lean_mkIff___closed__2);
v___x_5947_ = l_Lean_mkAppB(v___x_5946_, v_p_5944_, v_q_5945_);
return v___x_5947_;
}
}
static lean_object* _init_l_Lean_Nat_mkType(void){
_start:
{
lean_object* v___x_5948_; 
v___x_5948_ = lean_obj_once(&l_Lean_Literal_type___closed__2, &l_Lean_Literal_type___closed__2_once, _init_l_Lean_Literal_type___closed__2);
return v___x_5948_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5952_ = lean_box(0);
v___x_5953_ = ((lean_object*)(l_Lean_Nat_mkInstAdd___closed__1));
v___x_5954_ = l_Lean_Expr_const___override(v___x_5953_, v___x_5952_);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstAdd(void){
_start:
{
lean_object* v___x_5955_; 
v___x_5955_ = lean_obj_once(&l_Lean_Nat_mkInstAdd___closed__2, &l_Lean_Nat_mkInstAdd___closed__2_once, _init_l_Lean_Nat_mkInstAdd___closed__2);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__2(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5959_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5960_ = ((lean_object*)(l_Lean_Nat_mkInstHAdd___closed__1));
v___x_5961_ = l_Lean_Expr_const___override(v___x_5960_, v___x_5959_);
return v___x_5961_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd___closed__3(void){
_start:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5962_ = l_Lean_Nat_mkInstAdd;
v___x_5963_ = l_Lean_Nat_mkType;
v___x_5964_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_5965_ = l_Lean_mkAppB(v___x_5964_, v___x_5963_, v___x_5962_);
return v___x_5965_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHAdd(void){
_start:
{
lean_object* v___x_5966_; 
v___x_5966_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__3, &l_Lean_Nat_mkInstHAdd___closed__3_once, _init_l_Lean_Nat_mkInstHAdd___closed__3);
return v___x_5966_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; 
v___x_5970_ = lean_box(0);
v___x_5971_ = ((lean_object*)(l_Lean_Nat_mkInstSub___closed__1));
v___x_5972_ = l_Lean_Expr_const___override(v___x_5971_, v___x_5970_);
return v___x_5972_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstSub(void){
_start:
{
lean_object* v___x_5973_; 
v___x_5973_ = lean_obj_once(&l_Lean_Nat_mkInstSub___closed__2, &l_Lean_Nat_mkInstSub___closed__2_once, _init_l_Lean_Nat_mkInstSub___closed__2);
return v___x_5973_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__2(void){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5977_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5978_ = ((lean_object*)(l_Lean_Nat_mkInstHSub___closed__1));
v___x_5979_ = l_Lean_Expr_const___override(v___x_5978_, v___x_5977_);
return v___x_5979_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub___closed__3(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5980_ = l_Lean_Nat_mkInstSub;
v___x_5981_ = l_Lean_Nat_mkType;
v___x_5982_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_5983_ = l_Lean_mkAppB(v___x_5982_, v___x_5981_, v___x_5980_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHSub(void){
_start:
{
lean_object* v___x_5984_; 
v___x_5984_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__3, &l_Lean_Nat_mkInstHSub___closed__3_once, _init_l_Lean_Nat_mkInstHSub___closed__3);
return v___x_5984_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5988_ = lean_box(0);
v___x_5989_ = ((lean_object*)(l_Lean_Nat_mkInstMul___closed__1));
v___x_5990_ = l_Lean_Expr_const___override(v___x_5989_, v___x_5988_);
return v___x_5990_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMul(void){
_start:
{
lean_object* v___x_5991_; 
v___x_5991_ = lean_obj_once(&l_Lean_Nat_mkInstMul___closed__2, &l_Lean_Nat_mkInstMul___closed__2_once, _init_l_Lean_Nat_mkInstMul___closed__2);
return v___x_5991_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__2(void){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5995_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_5996_ = ((lean_object*)(l_Lean_Nat_mkInstHMul___closed__1));
v___x_5997_ = l_Lean_Expr_const___override(v___x_5996_, v___x_5995_);
return v___x_5997_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_5998_ = l_Lean_Nat_mkInstMul;
v___x_5999_ = l_Lean_Nat_mkType;
v___x_6000_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6001_ = l_Lean_mkAppB(v___x_6000_, v___x_5999_, v___x_5998_);
return v___x_6001_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMul(void){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__3, &l_Lean_Nat_mkInstHMul___closed__3_once, _init_l_Lean_Nat_mkInstHMul___closed__3);
return v___x_6002_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv___closed__2(void){
_start:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6007_ = lean_box(0);
v___x_6008_ = ((lean_object*)(l_Lean_Nat_mkInstDiv___closed__1));
v___x_6009_ = l_Lean_Expr_const___override(v___x_6008_, v___x_6007_);
return v___x_6009_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstDiv(void){
_start:
{
lean_object* v___x_6010_; 
v___x_6010_ = lean_obj_once(&l_Lean_Nat_mkInstDiv___closed__2, &l_Lean_Nat_mkInstDiv___closed__2_once, _init_l_Lean_Nat_mkInstDiv___closed__2);
return v___x_6010_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__2(void){
_start:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6014_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6015_ = ((lean_object*)(l_Lean_Nat_mkInstHDiv___closed__1));
v___x_6016_ = l_Lean_Expr_const___override(v___x_6015_, v___x_6014_);
return v___x_6016_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv___closed__3(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6017_ = l_Lean_Nat_mkInstDiv;
v___x_6018_ = l_Lean_Nat_mkType;
v___x_6019_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6020_ = l_Lean_mkAppB(v___x_6019_, v___x_6018_, v___x_6017_);
return v___x_6020_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHDiv(void){
_start:
{
lean_object* v___x_6021_; 
v___x_6021_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__3, &l_Lean_Nat_mkInstHDiv___closed__3_once, _init_l_Lean_Nat_mkInstHDiv___closed__3);
return v___x_6021_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod___closed__2(void){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6026_ = lean_box(0);
v___x_6027_ = ((lean_object*)(l_Lean_Nat_mkInstMod___closed__1));
v___x_6028_ = l_Lean_Expr_const___override(v___x_6027_, v___x_6026_);
return v___x_6028_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstMod(void){
_start:
{
lean_object* v___x_6029_; 
v___x_6029_ = lean_obj_once(&l_Lean_Nat_mkInstMod___closed__2, &l_Lean_Nat_mkInstMod___closed__2_once, _init_l_Lean_Nat_mkInstMod___closed__2);
return v___x_6029_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__2(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6033_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6034_ = ((lean_object*)(l_Lean_Nat_mkInstHMod___closed__1));
v___x_6035_ = l_Lean_Expr_const___override(v___x_6034_, v___x_6033_);
return v___x_6035_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod___closed__3(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6036_ = l_Lean_Nat_mkInstMod;
v___x_6037_ = l_Lean_Nat_mkType;
v___x_6038_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6039_ = l_Lean_mkAppB(v___x_6038_, v___x_6037_, v___x_6036_);
return v___x_6039_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHMod(void){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__3, &l_Lean_Nat_mkInstHMod___closed__3_once, _init_l_Lean_Nat_mkInstHMod___closed__3);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow___closed__2(void){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6044_ = lean_box(0);
v___x_6045_ = ((lean_object*)(l_Lean_Nat_mkInstNatPow___closed__1));
v___x_6046_ = l_Lean_Expr_const___override(v___x_6045_, v___x_6044_);
return v___x_6046_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstNatPow(void){
_start:
{
lean_object* v___x_6047_; 
v___x_6047_ = lean_obj_once(&l_Lean_Nat_mkInstNatPow___closed__2, &l_Lean_Nat_mkInstNatPow___closed__2_once, _init_l_Lean_Nat_mkInstNatPow___closed__2);
return v___x_6047_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6051_ = ((lean_object*)(l_Lean_mkNatLitCore___closed__3));
v___x_6052_ = ((lean_object*)(l_Lean_Nat_mkInstPow___closed__1));
v___x_6053_ = l_Lean_Expr_const___override(v___x_6052_, v___x_6051_);
return v___x_6053_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow___closed__3(void){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; 
v___x_6054_ = l_Lean_Nat_mkInstNatPow;
v___x_6055_ = l_Lean_Nat_mkType;
v___x_6056_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6057_ = l_Lean_mkAppB(v___x_6056_, v___x_6055_, v___x_6054_);
return v___x_6057_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstPow(void){
_start:
{
lean_object* v___x_6058_; 
v___x_6058_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__3, &l_Lean_Nat_mkInstPow___closed__3_once, _init_l_Lean_Nat_mkInstPow___closed__3);
return v___x_6058_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__3(void){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; 
v___x_6065_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__2));
v___x_6066_ = ((lean_object*)(l_Lean_Nat_mkInstHPow___closed__1));
v___x_6067_ = l_Lean_Expr_const___override(v___x_6066_, v___x_6065_);
return v___x_6067_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow___closed__4(void){
_start:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6068_ = l_Lean_Nat_mkInstPow;
v___x_6069_ = l_Lean_Nat_mkType;
v___x_6070_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6071_ = l_Lean_mkApp3(v___x_6070_, v___x_6069_, v___x_6069_, v___x_6068_);
return v___x_6071_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstHPow(void){
_start:
{
lean_object* v___x_6072_; 
v___x_6072_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__4, &l_Lean_Nat_mkInstHPow___closed__4_once, _init_l_Lean_Nat_mkInstHPow___closed__4);
return v___x_6072_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6076_ = lean_box(0);
v___x_6077_ = ((lean_object*)(l_Lean_Nat_mkInstLT___closed__1));
v___x_6078_ = l_Lean_Expr_const___override(v___x_6077_, v___x_6076_);
return v___x_6078_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLT(void){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = lean_obj_once(&l_Lean_Nat_mkInstLT___closed__2, &l_Lean_Nat_mkInstLT___closed__2_once, _init_l_Lean_Nat_mkInstLT___closed__2);
return v___x_6079_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6083_ = lean_box(0);
v___x_6084_ = ((lean_object*)(l_Lean_Nat_mkInstLE___closed__1));
v___x_6085_ = l_Lean_Expr_const___override(v___x_6084_, v___x_6083_);
return v___x_6085_;
}
}
static lean_object* _init_l_Lean_Nat_mkInstLE(void){
_start:
{
lean_object* v___x_6086_; 
v___x_6086_ = lean_obj_once(&l_Lean_Nat_mkInstLE___closed__2, &l_Lean_Nat_mkInstLE___closed__2_once, _init_l_Lean_Nat_mkInstLE___closed__2);
return v___x_6086_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3(void){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = lean_unsigned_to_nat(0u);
v___x_6093_ = l_Lean_Level_ofNat(v___x_6092_);
return v___x_6093_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4(void){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = lean_box(0);
v___x_6095_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
lean_ctor_set(v___x_6096_, 1, v___x_6094_);
return v___x_6096_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5(void){
_start:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6098_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
lean_ctor_set(v___x_6099_, 1, v___x_6097_);
return v___x_6099_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6100_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__5, &l___private_Lean_Expr_0__Lean_natAddFn___closed__5_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__5);
v___x_6101_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_6100_);
return v___x_6102_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7(void){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6103_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6104_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natAddFn___closed__2));
v___x_6105_ = l_Lean_Expr_const___override(v___x_6104_, v___x_6103_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; 
v___x_6106_ = l_Lean_Nat_mkInstHAdd;
v___x_6107_ = l_Lean_Nat_mkType;
v___x_6108_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6109_ = l_Lean_mkApp4(v___x_6108_, v___x_6107_, v___x_6107_, v___x_6107_, v___x_6106_);
return v___x_6109_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natAddFn(void){
_start:
{
lean_object* v___x_6110_; 
v___x_6110_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__8, &l___private_Lean_Expr_0__Lean_natAddFn___closed__8_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__8);
return v___x_6110_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6116_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6117_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natSubFn___closed__2));
v___x_6118_ = l_Lean_Expr_const___override(v___x_6117_, v___x_6116_);
return v___x_6118_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4(void){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6119_ = l_Lean_Nat_mkInstHSub;
v___x_6120_ = l_Lean_Nat_mkType;
v___x_6121_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6122_ = l_Lean_mkApp4(v___x_6121_, v___x_6120_, v___x_6120_, v___x_6120_, v___x_6119_);
return v___x_6122_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natSubFn(void){
_start:
{
lean_object* v___x_6123_; 
v___x_6123_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__4, &l___private_Lean_Expr_0__Lean_natSubFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__4);
return v___x_6123_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3(void){
_start:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6129_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6130_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natMulFn___closed__2));
v___x_6131_ = l_Lean_Expr_const___override(v___x_6130_, v___x_6129_);
return v___x_6131_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4(void){
_start:
{
lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6132_ = l_Lean_Nat_mkInstHMul;
v___x_6133_ = l_Lean_Nat_mkType;
v___x_6134_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6135_ = l_Lean_mkApp4(v___x_6134_, v___x_6133_, v___x_6133_, v___x_6133_, v___x_6132_);
return v___x_6135_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natMulFn(void){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__4, &l___private_Lean_Expr_0__Lean_natMulFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__4);
return v___x_6136_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3(void){
_start:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; 
v___x_6142_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6143_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natPowFn___closed__2));
v___x_6144_ = l_Lean_Expr_const___override(v___x_6143_, v___x_6142_);
return v___x_6144_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4(void){
_start:
{
lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6145_ = l_Lean_Nat_mkInstHPow;
v___x_6146_ = l_Lean_Nat_mkType;
v___x_6147_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6148_ = l_Lean_mkApp4(v___x_6147_, v___x_6146_, v___x_6146_, v___x_6146_, v___x_6145_);
return v___x_6148_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natPowFn(void){
_start:
{
lean_object* v___x_6149_; 
v___x_6149_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__4, &l___private_Lean_Expr_0__Lean_natPowFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__4);
return v___x_6149_;
}
}
static lean_object* _init_l_Lean_mkNatSucc___closed__2(void){
_start:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6154_ = lean_box(0);
v___x_6155_ = ((lean_object*)(l_Lean_mkNatSucc___closed__1));
v___x_6156_ = l_Lean_Expr_const___override(v___x_6155_, v___x_6154_);
return v___x_6156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSucc(lean_object* v_a_6157_){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6158_ = lean_obj_once(&l_Lean_mkNatSucc___closed__2, &l_Lean_mkNatSucc___closed__2_once, _init_l_Lean_mkNatSucc___closed__2);
v___x_6159_ = l_Lean_Expr_app___override(v___x_6158_, v_a_6157_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatAdd(lean_object* v_a_6160_, lean_object* v_b_6161_){
_start:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6162_ = l___private_Lean_Expr_0__Lean_natAddFn;
v___x_6163_ = l_Lean_mkAppB(v___x_6162_, v_a_6160_, v_b_6161_);
return v___x_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatSub(lean_object* v_a_6164_, lean_object* v_b_6165_){
_start:
{
lean_object* v___x_6166_; lean_object* v___x_6167_; 
v___x_6166_ = l___private_Lean_Expr_0__Lean_natSubFn;
v___x_6167_ = l_Lean_mkAppB(v___x_6166_, v_a_6164_, v_b_6165_);
return v___x_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMul(lean_object* v_a_6168_, lean_object* v_b_6169_){
_start:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6170_ = l___private_Lean_Expr_0__Lean_natMulFn;
v___x_6171_ = l_Lean_mkAppB(v___x_6170_, v_a_6168_, v_b_6169_);
return v___x_6171_;
}
}
static lean_object* _init_l_Lean_mkNatDiv___closed__3(void){
_start:
{
lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6177_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6178_ = ((lean_object*)(l_Lean_mkNatDiv___closed__2));
v___x_6179_ = l_Lean_Expr_const___override(v___x_6178_, v___x_6177_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatDiv(lean_object* v_a_6180_, lean_object* v_b_6181_){
_start:
{
lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v___x_6182_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6183_ = l_Lean_Nat_mkType;
v___x_6184_ = l_Lean_Nat_mkInstHDiv;
v___x_6185_ = l_Lean_mkApp6(v___x_6182_, v___x_6183_, v___x_6183_, v___x_6183_, v___x_6184_, v_a_6180_, v_b_6181_);
return v___x_6185_;
}
}
static lean_object* _init_l_Lean_mkNatMod___closed__3(void){
_start:
{
lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6191_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__6, &l___private_Lean_Expr_0__Lean_natAddFn___closed__6_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__6);
v___x_6192_ = ((lean_object*)(l_Lean_mkNatMod___closed__2));
v___x_6193_ = l_Lean_Expr_const___override(v___x_6192_, v___x_6191_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatMod(lean_object* v_a_6194_, lean_object* v_b_6195_){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6196_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6197_ = l_Lean_Nat_mkType;
v___x_6198_ = l_Lean_Nat_mkInstHMod;
v___x_6199_ = l_Lean_mkApp6(v___x_6196_, v___x_6197_, v___x_6197_, v___x_6197_, v___x_6198_, v_a_6194_, v_b_6195_);
return v___x_6199_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatPow(lean_object* v_a_6200_, lean_object* v_b_6201_){
_start:
{
lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6202_ = l___private_Lean_Expr_0__Lean_natPowFn;
v___x_6203_ = l_Lean_mkAppB(v___x_6202_, v_a_6200_, v_b_6201_);
return v___x_6203_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3(void){
_start:
{
lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v___x_6209_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6210_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_natLEPred___closed__2));
v___x_6211_ = l_Lean_Expr_const___override(v___x_6210_, v___x_6209_);
return v___x_6211_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4(void){
_start:
{
lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6212_ = l_Lean_Nat_mkInstLE;
v___x_6213_ = l_Lean_Nat_mkType;
v___x_6214_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6215_ = l_Lean_mkAppB(v___x_6214_, v___x_6213_, v___x_6212_);
return v___x_6215_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natLEPred(void){
_start:
{
lean_object* v___x_6216_; 
v___x_6216_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__4, &l___private_Lean_Expr_0__Lean_natLEPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__4);
return v___x_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLE(lean_object* v_a_6217_, lean_object* v_b_6218_){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; 
v___x_6219_ = l___private_Lean_Expr_0__Lean_natLEPred;
v___x_6220_ = l_Lean_mkAppB(v___x_6219_, v_a_6217_, v_b_6218_);
return v___x_6220_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0(void){
_start:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; 
v___x_6221_ = lean_unsigned_to_nat(1u);
v___x_6222_ = l_Lean_Level_ofNat(v___x_6221_);
return v___x_6222_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1(void){
_start:
{
lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6223_ = lean_box(0);
v___x_6224_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__0, &l___private_Lean_Expr_0__Lean_natEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__0);
v___x_6225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6224_);
lean_ctor_set(v___x_6225_, 1, v___x_6223_);
return v___x_6225_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2(void){
_start:
{
lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6226_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__1, &l___private_Lean_Expr_0__Lean_natEqPred___closed__1_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__1);
v___x_6227_ = ((lean_object*)(l_Lean_isLHSGoal_x3f___closed__1));
v___x_6228_ = l_Lean_Expr_const___override(v___x_6227_, v___x_6226_);
return v___x_6228_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3(void){
_start:
{
lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; 
v___x_6229_ = l_Lean_Nat_mkType;
v___x_6230_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6231_ = l_Lean_Expr_app___override(v___x_6230_, v___x_6229_);
return v___x_6231_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_natEqPred(void){
_start:
{
lean_object* v___x_6232_; 
v___x_6232_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__3, &l___private_Lean_Expr_0__Lean_natEqPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__3);
return v___x_6232_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatEq(lean_object* v_a_6233_, lean_object* v_b_6234_){
_start:
{
lean_object* v___x_6235_; lean_object* v___x_6236_; 
v___x_6235_ = l___private_Lean_Expr_0__Lean_natEqPred;
v___x_6236_ = l_Lean_mkAppB(v___x_6235_, v_a_6233_, v_b_6234_);
return v___x_6236_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__0(void){
_start:
{
lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6237_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__3, &l___private_Lean_Expr_0__Lean_natAddFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__3);
v___x_6238_ = l_Lean_Expr_sort___override(v___x_6237_);
return v___x_6238_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq___closed__1(void){
_start:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; 
v___x_6239_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__0, &l___private_Lean_Expr_0__Lean_propEq___closed__0_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__0);
v___x_6240_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6241_ = l_Lean_Expr_app___override(v___x_6240_, v___x_6239_);
return v___x_6241_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_propEq(void){
_start:
{
lean_object* v___x_6242_; 
v___x_6242_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_propEq___closed__1, &l___private_Lean_Expr_0__Lean_propEq___closed__1_once, _init_l___private_Lean_Expr_0__Lean_propEq___closed__1);
return v___x_6242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPropEq(lean_object* v_a_6243_, lean_object* v_b_6244_){
_start:
{
lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6245_ = l___private_Lean_Expr_0__Lean_propEq;
v___x_6246_ = l_Lean_mkAppB(v___x_6245_, v_a_6243_, v_b_6244_);
return v___x_6246_;
}
}
static lean_object* _init_l_Lean_Int_mkType___closed__2(void){
_start:
{
lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6250_ = lean_box(0);
v___x_6251_ = ((lean_object*)(l_Lean_Int_mkType___closed__1));
v___x_6252_ = l_Lean_Expr_const___override(v___x_6251_, v___x_6250_);
return v___x_6252_;
}
}
static lean_object* _init_l_Lean_Int_mkType(void){
_start:
{
lean_object* v___x_6253_; 
v___x_6253_ = lean_obj_once(&l_Lean_Int_mkType___closed__2, &l_Lean_Int_mkType___closed__2_once, _init_l_Lean_Int_mkType___closed__2);
return v___x_6253_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg___closed__2(void){
_start:
{
lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; 
v___x_6258_ = lean_box(0);
v___x_6259_ = ((lean_object*)(l_Lean_Int_mkInstNeg___closed__1));
v___x_6260_ = l_Lean_Expr_const___override(v___x_6259_, v___x_6258_);
return v___x_6260_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNeg(void){
_start:
{
lean_object* v___x_6261_; 
v___x_6261_ = lean_obj_once(&l_Lean_Int_mkInstNeg___closed__2, &l_Lean_Int_mkInstNeg___closed__2_once, _init_l_Lean_Int_mkInstNeg___closed__2);
return v___x_6261_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd___closed__2(void){
_start:
{
lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; 
v___x_6266_ = lean_box(0);
v___x_6267_ = ((lean_object*)(l_Lean_Int_mkInstAdd___closed__1));
v___x_6268_ = l_Lean_Expr_const___override(v___x_6267_, v___x_6266_);
return v___x_6268_;
}
}
static lean_object* _init_l_Lean_Int_mkInstAdd(void){
_start:
{
lean_object* v___x_6269_; 
v___x_6269_ = lean_obj_once(&l_Lean_Int_mkInstAdd___closed__2, &l_Lean_Int_mkInstAdd___closed__2_once, _init_l_Lean_Int_mkInstAdd___closed__2);
return v___x_6269_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd___closed__0(void){
_start:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6270_ = l_Lean_Int_mkInstAdd;
v___x_6271_ = l_Lean_Int_mkType;
v___x_6272_ = lean_obj_once(&l_Lean_Nat_mkInstHAdd___closed__2, &l_Lean_Nat_mkInstHAdd___closed__2_once, _init_l_Lean_Nat_mkInstHAdd___closed__2);
v___x_6273_ = l_Lean_mkAppB(v___x_6272_, v___x_6271_, v___x_6270_);
return v___x_6273_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHAdd(void){
_start:
{
lean_object* v___x_6274_; 
v___x_6274_ = lean_obj_once(&l_Lean_Int_mkInstHAdd___closed__0, &l_Lean_Int_mkInstHAdd___closed__0_once, _init_l_Lean_Int_mkInstHAdd___closed__0);
return v___x_6274_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub___closed__2(void){
_start:
{
lean_object* v___x_6279_; lean_object* v___x_6280_; lean_object* v___x_6281_; 
v___x_6279_ = lean_box(0);
v___x_6280_ = ((lean_object*)(l_Lean_Int_mkInstSub___closed__1));
v___x_6281_ = l_Lean_Expr_const___override(v___x_6280_, v___x_6279_);
return v___x_6281_;
}
}
static lean_object* _init_l_Lean_Int_mkInstSub(void){
_start:
{
lean_object* v___x_6282_; 
v___x_6282_ = lean_obj_once(&l_Lean_Int_mkInstSub___closed__2, &l_Lean_Int_mkInstSub___closed__2_once, _init_l_Lean_Int_mkInstSub___closed__2);
return v___x_6282_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub___closed__0(void){
_start:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; 
v___x_6283_ = l_Lean_Int_mkInstSub;
v___x_6284_ = l_Lean_Int_mkType;
v___x_6285_ = lean_obj_once(&l_Lean_Nat_mkInstHSub___closed__2, &l_Lean_Nat_mkInstHSub___closed__2_once, _init_l_Lean_Nat_mkInstHSub___closed__2);
v___x_6286_ = l_Lean_mkAppB(v___x_6285_, v___x_6284_, v___x_6283_);
return v___x_6286_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHSub(void){
_start:
{
lean_object* v___x_6287_; 
v___x_6287_ = lean_obj_once(&l_Lean_Int_mkInstHSub___closed__0, &l_Lean_Int_mkInstHSub___closed__0_once, _init_l_Lean_Int_mkInstHSub___closed__0);
return v___x_6287_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; 
v___x_6292_ = lean_box(0);
v___x_6293_ = ((lean_object*)(l_Lean_Int_mkInstMul___closed__1));
v___x_6294_ = l_Lean_Expr_const___override(v___x_6293_, v___x_6292_);
return v___x_6294_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMul(void){
_start:
{
lean_object* v___x_6295_; 
v___x_6295_ = lean_obj_once(&l_Lean_Int_mkInstMul___closed__2, &l_Lean_Int_mkInstMul___closed__2_once, _init_l_Lean_Int_mkInstMul___closed__2);
return v___x_6295_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul___closed__0(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6296_ = l_Lean_Int_mkInstMul;
v___x_6297_ = l_Lean_Int_mkType;
v___x_6298_ = lean_obj_once(&l_Lean_Nat_mkInstHMul___closed__2, &l_Lean_Nat_mkInstHMul___closed__2_once, _init_l_Lean_Nat_mkInstHMul___closed__2);
v___x_6299_ = l_Lean_mkAppB(v___x_6298_, v___x_6297_, v___x_6296_);
return v___x_6299_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMul(void){
_start:
{
lean_object* v___x_6300_; 
v___x_6300_ = lean_obj_once(&l_Lean_Int_mkInstHMul___closed__0, &l_Lean_Int_mkInstHMul___closed__0_once, _init_l_Lean_Int_mkInstHMul___closed__0);
return v___x_6300_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv___closed__1(void){
_start:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6304_ = lean_box(0);
v___x_6305_ = ((lean_object*)(l_Lean_Int_mkInstDiv___closed__0));
v___x_6306_ = l_Lean_Expr_const___override(v___x_6305_, v___x_6304_);
return v___x_6306_;
}
}
static lean_object* _init_l_Lean_Int_mkInstDiv(void){
_start:
{
lean_object* v___x_6307_; 
v___x_6307_ = lean_obj_once(&l_Lean_Int_mkInstDiv___closed__1, &l_Lean_Int_mkInstDiv___closed__1_once, _init_l_Lean_Int_mkInstDiv___closed__1);
return v___x_6307_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv___closed__0(void){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; 
v___x_6308_ = l_Lean_Int_mkInstDiv;
v___x_6309_ = l_Lean_Int_mkType;
v___x_6310_ = lean_obj_once(&l_Lean_Nat_mkInstHDiv___closed__2, &l_Lean_Nat_mkInstHDiv___closed__2_once, _init_l_Lean_Nat_mkInstHDiv___closed__2);
v___x_6311_ = l_Lean_mkAppB(v___x_6310_, v___x_6309_, v___x_6308_);
return v___x_6311_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHDiv(void){
_start:
{
lean_object* v___x_6312_; 
v___x_6312_ = lean_obj_once(&l_Lean_Int_mkInstHDiv___closed__0, &l_Lean_Int_mkInstHDiv___closed__0_once, _init_l_Lean_Int_mkInstHDiv___closed__0);
return v___x_6312_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod___closed__1(void){
_start:
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6316_ = lean_box(0);
v___x_6317_ = ((lean_object*)(l_Lean_Int_mkInstMod___closed__0));
v___x_6318_ = l_Lean_Expr_const___override(v___x_6317_, v___x_6316_);
return v___x_6318_;
}
}
static lean_object* _init_l_Lean_Int_mkInstMod(void){
_start:
{
lean_object* v___x_6319_; 
v___x_6319_ = lean_obj_once(&l_Lean_Int_mkInstMod___closed__1, &l_Lean_Int_mkInstMod___closed__1_once, _init_l_Lean_Int_mkInstMod___closed__1);
return v___x_6319_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod___closed__0(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; 
v___x_6320_ = l_Lean_Int_mkInstMod;
v___x_6321_ = l_Lean_Int_mkType;
v___x_6322_ = lean_obj_once(&l_Lean_Nat_mkInstHMod___closed__2, &l_Lean_Nat_mkInstHMod___closed__2_once, _init_l_Lean_Nat_mkInstHMod___closed__2);
v___x_6323_ = l_Lean_mkAppB(v___x_6322_, v___x_6321_, v___x_6320_);
return v___x_6323_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHMod(void){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = lean_obj_once(&l_Lean_Int_mkInstHMod___closed__0, &l_Lean_Int_mkInstHMod___closed__0_once, _init_l_Lean_Int_mkInstHMod___closed__0);
return v___x_6324_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow___closed__2(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_box(0);
v___x_6330_ = ((lean_object*)(l_Lean_Int_mkInstPow___closed__1));
v___x_6331_ = l_Lean_Expr_const___override(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPow(void){
_start:
{
lean_object* v___x_6332_; 
v___x_6332_ = lean_obj_once(&l_Lean_Int_mkInstPow___closed__2, &l_Lean_Int_mkInstPow___closed__2_once, _init_l_Lean_Int_mkInstPow___closed__2);
return v___x_6332_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat___closed__0(void){
_start:
{
lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; 
v___x_6333_ = l_Lean_Int_mkInstPow;
v___x_6334_ = l_Lean_Int_mkType;
v___x_6335_ = lean_obj_once(&l_Lean_Nat_mkInstPow___closed__2, &l_Lean_Nat_mkInstPow___closed__2_once, _init_l_Lean_Nat_mkInstPow___closed__2);
v___x_6336_ = l_Lean_mkAppB(v___x_6335_, v___x_6334_, v___x_6333_);
return v___x_6336_;
}
}
static lean_object* _init_l_Lean_Int_mkInstPowNat(void){
_start:
{
lean_object* v___x_6337_; 
v___x_6337_ = lean_obj_once(&l_Lean_Int_mkInstPowNat___closed__0, &l_Lean_Int_mkInstPowNat___closed__0_once, _init_l_Lean_Int_mkInstPowNat___closed__0);
return v___x_6337_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow___closed__0(void){
_start:
{
lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; 
v___x_6338_ = l_Lean_Int_mkInstPowNat;
v___x_6339_ = l_Lean_Nat_mkType;
v___x_6340_ = l_Lean_Int_mkType;
v___x_6341_ = lean_obj_once(&l_Lean_Nat_mkInstHPow___closed__3, &l_Lean_Nat_mkInstHPow___closed__3_once, _init_l_Lean_Nat_mkInstHPow___closed__3);
v___x_6342_ = l_Lean_mkApp3(v___x_6341_, v___x_6340_, v___x_6339_, v___x_6338_);
return v___x_6342_;
}
}
static lean_object* _init_l_Lean_Int_mkInstHPow(void){
_start:
{
lean_object* v___x_6343_; 
v___x_6343_ = lean_obj_once(&l_Lean_Int_mkInstHPow___closed__0, &l_Lean_Int_mkInstHPow___closed__0_once, _init_l_Lean_Int_mkInstHPow___closed__0);
return v___x_6343_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT___closed__2(void){
_start:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6348_ = lean_box(0);
v___x_6349_ = ((lean_object*)(l_Lean_Int_mkInstLT___closed__1));
v___x_6350_ = l_Lean_Expr_const___override(v___x_6349_, v___x_6348_);
return v___x_6350_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLT(void){
_start:
{
lean_object* v___x_6351_; 
v___x_6351_ = lean_obj_once(&l_Lean_Int_mkInstLT___closed__2, &l_Lean_Int_mkInstLT___closed__2_once, _init_l_Lean_Int_mkInstLT___closed__2);
return v___x_6351_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE___closed__2(void){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; 
v___x_6356_ = lean_box(0);
v___x_6357_ = ((lean_object*)(l_Lean_Int_mkInstLE___closed__1));
v___x_6358_ = l_Lean_Expr_const___override(v___x_6357_, v___x_6356_);
return v___x_6358_;
}
}
static lean_object* _init_l_Lean_Int_mkInstLE(void){
_start:
{
lean_object* v___x_6359_; 
v___x_6359_ = lean_obj_once(&l_Lean_Int_mkInstLE___closed__2, &l_Lean_Int_mkInstLE___closed__2_once, _init_l_Lean_Int_mkInstLE___closed__2);
return v___x_6359_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast___closed__2(void){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6363_ = lean_box(0);
v___x_6364_ = ((lean_object*)(l_Lean_Int_mkInstNatCast___closed__1));
v___x_6365_ = l_Lean_Expr_const___override(v___x_6364_, v___x_6363_);
return v___x_6365_;
}
}
static lean_object* _init_l_Lean_Int_mkInstNatCast(void){
_start:
{
lean_object* v___x_6366_; 
v___x_6366_ = lean_obj_once(&l_Lean_Int_mkInstNatCast___closed__2, &l_Lean_Int_mkInstNatCast___closed__2_once, _init_l_Lean_Int_mkInstNatCast___closed__2);
return v___x_6366_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6367_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6368_ = ((lean_object*)(l_Lean_Expr_int_x3f___closed__2));
v___x_6369_ = l_Lean_Expr_const___override(v___x_6368_, v___x_6367_);
return v___x_6369_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1(void){
_start:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6370_ = l_Lean_Int_mkInstNeg;
v___x_6371_ = l_Lean_Int_mkType;
v___x_6372_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__0, &l___private_Lean_Expr_0__Lean_intNegFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__0);
v___x_6373_ = l_Lean_mkAppB(v___x_6372_, v___x_6371_, v___x_6370_);
return v___x_6373_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNegFn(void){
_start:
{
lean_object* v___x_6374_; 
v___x_6374_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNegFn___closed__1, &l___private_Lean_Expr_0__Lean_intNegFn___closed__1_once, _init_l___private_Lean_Expr_0__Lean_intNegFn___closed__1);
return v___x_6374_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0(void){
_start:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; 
v___x_6375_ = l_Lean_Int_mkInstHAdd;
v___x_6376_ = l_Lean_Int_mkType;
v___x_6377_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__7, &l___private_Lean_Expr_0__Lean_natAddFn___closed__7_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__7);
v___x_6378_ = l_Lean_mkApp4(v___x_6377_, v___x_6376_, v___x_6376_, v___x_6376_, v___x_6375_);
return v___x_6378_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intAddFn(void){
_start:
{
lean_object* v___x_6379_; 
v___x_6379_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intAddFn___closed__0, &l___private_Lean_Expr_0__Lean_intAddFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intAddFn___closed__0);
return v___x_6379_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0(void){
_start:
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6380_ = l_Lean_Int_mkInstHSub;
v___x_6381_ = l_Lean_Int_mkType;
v___x_6382_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natSubFn___closed__3, &l___private_Lean_Expr_0__Lean_natSubFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natSubFn___closed__3);
v___x_6383_ = l_Lean_mkApp4(v___x_6382_, v___x_6381_, v___x_6381_, v___x_6381_, v___x_6380_);
return v___x_6383_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intSubFn(void){
_start:
{
lean_object* v___x_6384_; 
v___x_6384_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intSubFn___closed__0, &l___private_Lean_Expr_0__Lean_intSubFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intSubFn___closed__0);
return v___x_6384_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0(void){
_start:
{
lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6385_ = l_Lean_Int_mkInstHMul;
v___x_6386_ = l_Lean_Int_mkType;
v___x_6387_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natMulFn___closed__3, &l___private_Lean_Expr_0__Lean_natMulFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natMulFn___closed__3);
v___x_6388_ = l_Lean_mkApp4(v___x_6387_, v___x_6386_, v___x_6386_, v___x_6386_, v___x_6385_);
return v___x_6388_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intMulFn(void){
_start:
{
lean_object* v___x_6389_; 
v___x_6389_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intMulFn___closed__0, &l___private_Lean_Expr_0__Lean_intMulFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intMulFn___closed__0);
return v___x_6389_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0(void){
_start:
{
lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6390_ = l_Lean_Int_mkInstHDiv;
v___x_6391_ = l_Lean_Int_mkType;
v___x_6392_ = lean_obj_once(&l_Lean_mkNatDiv___closed__3, &l_Lean_mkNatDiv___closed__3_once, _init_l_Lean_mkNatDiv___closed__3);
v___x_6393_ = l_Lean_mkApp4(v___x_6392_, v___x_6391_, v___x_6391_, v___x_6391_, v___x_6390_);
return v___x_6393_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intDivFn(void){
_start:
{
lean_object* v___x_6394_; 
v___x_6394_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intDivFn___closed__0, &l___private_Lean_Expr_0__Lean_intDivFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intDivFn___closed__0);
return v___x_6394_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0(void){
_start:
{
lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; 
v___x_6395_ = l_Lean_Int_mkInstHMod;
v___x_6396_ = l_Lean_Int_mkType;
v___x_6397_ = lean_obj_once(&l_Lean_mkNatMod___closed__3, &l_Lean_mkNatMod___closed__3_once, _init_l_Lean_mkNatMod___closed__3);
v___x_6398_ = l_Lean_mkApp4(v___x_6397_, v___x_6396_, v___x_6396_, v___x_6396_, v___x_6395_);
return v___x_6398_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intModFn(void){
_start:
{
lean_object* v___x_6399_; 
v___x_6399_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intModFn___closed__0, &l___private_Lean_Expr_0__Lean_intModFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intModFn___closed__0);
return v___x_6399_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0(void){
_start:
{
lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; 
v___x_6400_ = l_Lean_Int_mkInstHPow;
v___x_6401_ = l_Lean_Nat_mkType;
v___x_6402_ = l_Lean_Int_mkType;
v___x_6403_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natPowFn___closed__3, &l___private_Lean_Expr_0__Lean_natPowFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natPowFn___closed__3);
v___x_6404_ = l_Lean_mkApp4(v___x_6403_, v___x_6402_, v___x_6401_, v___x_6402_, v___x_6400_);
return v___x_6404_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intPowNatFn(void){
_start:
{
lean_object* v___x_6405_; 
v___x_6405_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0, &l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intPowNatFn___closed__0);
return v___x_6405_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3(void){
_start:
{
lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; 
v___x_6411_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6412_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intNatCastFn___closed__2));
v___x_6413_ = l_Lean_Expr_const___override(v___x_6412_, v___x_6411_);
return v___x_6413_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4(void){
_start:
{
lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; 
v___x_6414_ = l_Lean_Int_mkInstNatCast;
v___x_6415_ = l_Lean_Int_mkType;
v___x_6416_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__3);
v___x_6417_ = l_Lean_mkAppB(v___x_6416_, v___x_6415_, v___x_6414_);
return v___x_6417_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intNatCastFn(void){
_start:
{
lean_object* v___x_6418_; 
v___x_6418_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4, &l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intNatCastFn___closed__4);
return v___x_6418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNeg(lean_object* v_a_6419_){
_start:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6420_ = l___private_Lean_Expr_0__Lean_intNegFn;
v___x_6421_ = l_Lean_Expr_app___override(v___x_6420_, v_a_6419_);
return v___x_6421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntAdd(lean_object* v_a_6422_, lean_object* v_b_6423_){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6424_ = l___private_Lean_Expr_0__Lean_intAddFn;
v___x_6425_ = l_Lean_mkAppB(v___x_6424_, v_a_6422_, v_b_6423_);
return v___x_6425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntSub(lean_object* v_a_6426_, lean_object* v_b_6427_){
_start:
{
lean_object* v___x_6428_; lean_object* v___x_6429_; 
v___x_6428_ = l___private_Lean_Expr_0__Lean_intSubFn;
v___x_6429_ = l_Lean_mkAppB(v___x_6428_, v_a_6426_, v_b_6427_);
return v___x_6429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMul(lean_object* v_a_6430_, lean_object* v_b_6431_){
_start:
{
lean_object* v___x_6432_; lean_object* v___x_6433_; 
v___x_6432_ = l___private_Lean_Expr_0__Lean_intMulFn;
v___x_6433_ = l_Lean_mkAppB(v___x_6432_, v_a_6430_, v_b_6431_);
return v___x_6433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDiv(lean_object* v_a_6434_, lean_object* v_b_6435_){
_start:
{
lean_object* v___x_6436_; lean_object* v___x_6437_; 
v___x_6436_ = l___private_Lean_Expr_0__Lean_intDivFn;
v___x_6437_ = l_Lean_mkAppB(v___x_6436_, v_a_6434_, v_b_6435_);
return v___x_6437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntMod(lean_object* v_a_6438_, lean_object* v_b_6439_){
_start:
{
lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6440_ = l___private_Lean_Expr_0__Lean_intModFn;
v___x_6441_ = l_Lean_mkAppB(v___x_6440_, v_a_6438_, v_b_6439_);
return v___x_6441_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntNatCast(lean_object* v_a_6442_){
_start:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; 
v___x_6443_ = l___private_Lean_Expr_0__Lean_intNatCastFn;
v___x_6444_ = l_Lean_Expr_app___override(v___x_6443_, v_a_6442_);
return v___x_6444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntPowNat(lean_object* v_a_6445_, lean_object* v_b_6446_){
_start:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; 
v___x_6447_ = l___private_Lean_Expr_0__Lean_intPowNatFn;
v___x_6448_ = l_Lean_mkAppB(v___x_6447_, v_a_6445_, v_b_6446_);
return v___x_6448_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0(void){
_start:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; 
v___x_6449_ = l_Lean_Int_mkInstLE;
v___x_6450_ = l_Lean_Int_mkType;
v___x_6451_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natLEPred___closed__3, &l___private_Lean_Expr_0__Lean_natLEPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_natLEPred___closed__3);
v___x_6452_ = l_Lean_mkAppB(v___x_6451_, v___x_6450_, v___x_6449_);
return v___x_6452_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLEPred(void){
_start:
{
lean_object* v___x_6453_; 
v___x_6453_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLEPred___closed__0, &l___private_Lean_Expr_0__Lean_intLEPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intLEPred___closed__0);
return v___x_6453_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLE(lean_object* v_a_6454_, lean_object* v_b_6455_){
_start:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = l___private_Lean_Expr_0__Lean_intLEPred;
v___x_6457_ = l_Lean_mkAppB(v___x_6456_, v_a_6454_, v_b_6455_);
return v___x_6457_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3(void){
_start:
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6463_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6464_ = ((lean_object*)(l___private_Lean_Expr_0__Lean_intLTPred___closed__2));
v___x_6465_ = l_Lean_Expr_const___override(v___x_6464_, v___x_6463_);
return v___x_6465_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6466_ = l_Lean_Int_mkInstLT;
v___x_6467_ = l_Lean_Int_mkType;
v___x_6468_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__3, &l___private_Lean_Expr_0__Lean_intLTPred___closed__3_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__3);
v___x_6469_ = l_Lean_mkAppB(v___x_6468_, v___x_6467_, v___x_6466_);
return v___x_6469_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intLTPred(void){
_start:
{
lean_object* v___x_6470_; 
v___x_6470_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intLTPred___closed__4, &l___private_Lean_Expr_0__Lean_intLTPred___closed__4_once, _init_l___private_Lean_Expr_0__Lean_intLTPred___closed__4);
return v___x_6470_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLT(lean_object* v_a_6471_, lean_object* v_b_6472_){
_start:
{
lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6473_ = l___private_Lean_Expr_0__Lean_intLTPred;
v___x_6474_ = l_Lean_mkAppB(v___x_6473_, v_a_6471_, v_b_6472_);
return v___x_6474_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0(void){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; 
v___x_6475_ = l_Lean_Int_mkType;
v___x_6476_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6477_ = l_Lean_Expr_app___override(v___x_6476_, v___x_6475_);
return v___x_6477_;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_intEqPred(void){
_start:
{
lean_object* v___x_6478_; 
v___x_6478_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_intEqPred___closed__0, &l___private_Lean_Expr_0__Lean_intEqPred___closed__0_once, _init_l___private_Lean_Expr_0__Lean_intEqPred___closed__0);
return v___x_6478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntEq(lean_object* v_a_6479_, lean_object* v_b_6480_){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6481_ = l___private_Lean_Expr_0__Lean_intEqPred;
v___x_6482_ = l_Lean_mkAppB(v___x_6481_, v_a_6479_, v_b_6480_);
return v___x_6482_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__3(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6488_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6489_ = ((lean_object*)(l_Lean_mkIntDvd___closed__2));
v___x_6490_ = l_Lean_Expr_const___override(v___x_6489_, v___x_6488_);
return v___x_6490_;
}
}
static lean_object* _init_l_Lean_mkIntDvd___closed__6(void){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6495_ = lean_box(0);
v___x_6496_ = ((lean_object*)(l_Lean_mkIntDvd___closed__5));
v___x_6497_ = l_Lean_Expr_const___override(v___x_6496_, v___x_6495_);
return v___x_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntDvd(lean_object* v_a_6498_, lean_object* v_b_6499_){
_start:
{
lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; 
v___x_6500_ = lean_obj_once(&l_Lean_mkIntDvd___closed__3, &l_Lean_mkIntDvd___closed__3_once, _init_l_Lean_mkIntDvd___closed__3);
v___x_6501_ = l_Lean_Int_mkType;
v___x_6502_ = lean_obj_once(&l_Lean_mkIntDvd___closed__6, &l_Lean_mkIntDvd___closed__6_once, _init_l_Lean_mkIntDvd___closed__6);
v___x_6503_ = l_Lean_mkApp4(v___x_6500_, v___x_6501_, v___x_6502_, v_a_6498_, v_b_6499_);
return v___x_6503_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__2(void){
_start:
{
lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; 
v___x_6507_ = lean_box(0);
v___x_6508_ = ((lean_object*)(l_Lean_mkIntLit___closed__1));
v___x_6509_ = l_Lean_Expr_const___override(v___x_6508_, v___x_6507_);
return v___x_6509_;
}
}
static lean_object* _init_l_Lean_mkIntLit___closed__3(void){
_start:
{
lean_object* v___x_6510_; lean_object* v___x_6511_; 
v___x_6510_ = lean_unsigned_to_nat(0u);
v___x_6511_ = lean_nat_to_int(v___x_6510_);
return v___x_6511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit(lean_object* v_n_6512_){
_start:
{
lean_object* v___x_6513_; lean_object* v_r_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v_r_6519_; lean_object* v___x_6520_; uint8_t v___x_6521_; 
v___x_6513_ = lean_nat_abs(v_n_6512_);
v_r_6514_ = l_Lean_mkRawNatLit(v___x_6513_);
v___x_6515_ = lean_obj_once(&l_Lean_mkNatLitCore___closed__4, &l_Lean_mkNatLitCore___closed__4_once, _init_l_Lean_mkNatLitCore___closed__4);
v___x_6516_ = l_Lean_Int_mkType;
v___x_6517_ = lean_obj_once(&l_Lean_mkIntLit___closed__2, &l_Lean_mkIntLit___closed__2_once, _init_l_Lean_mkIntLit___closed__2);
lean_inc_ref(v_r_6514_);
v___x_6518_ = l_Lean_Expr_app___override(v___x_6517_, v_r_6514_);
v_r_6519_ = l_Lean_mkApp3(v___x_6515_, v___x_6516_, v_r_6514_, v___x_6518_);
v___x_6520_ = lean_obj_once(&l_Lean_mkIntLit___closed__3, &l_Lean_mkIntLit___closed__3_once, _init_l_Lean_mkIntLit___closed__3);
v___x_6521_ = lean_int_dec_lt(v_n_6512_, v___x_6520_);
if (v___x_6521_ == 0)
{
return v_r_6519_;
}
else
{
lean_object* v___x_6522_; 
v___x_6522_ = l_Lean_mkIntNeg(v_r_6519_);
return v___x_6522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIntLit___boxed(lean_object* v_n_6523_){
_start:
{
lean_object* v_res_6524_; 
v_res_6524_ = l_Lean_mkIntLit(v_n_6523_);
lean_dec(v_n_6523_);
return v_res_6524_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6529_ = lean_box(0);
v___x_6530_ = l_Lean_Level_succ___override(v___x_6529_);
return v___x_6530_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; 
v___x_6531_ = lean_box(0);
v___x_6532_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__2, &l_Lean_reflBoolTrue___closed__2_once, _init_l_Lean_reflBoolTrue___closed__2);
v___x_6533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6533_, 0, v___x_6532_);
lean_ctor_set(v___x_6533_, 1, v___x_6531_);
return v___x_6533_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; 
v___x_6534_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__3, &l_Lean_reflBoolTrue___closed__3_once, _init_l_Lean_reflBoolTrue___closed__3);
v___x_6535_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__1));
v___x_6536_ = l_Lean_Expr_const___override(v___x_6535_, v___x_6534_);
return v___x_6536_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__6(void){
_start:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; 
v___x_6539_ = lean_box(0);
v___x_6540_ = ((lean_object*)(l_Lean_reflBoolTrue___closed__5));
v___x_6541_ = l_Lean_Expr_const___override(v___x_6540_, v___x_6539_);
return v___x_6541_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__7(void){
_start:
{
lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6542_ = lean_box(0);
v___x_6543_ = ((lean_object*)(l_Lean_Expr_isBoolTrue___closed__0));
v___x_6544_ = l_Lean_Expr_const___override(v___x_6543_, v___x_6542_);
return v___x_6544_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue___closed__8(void){
_start:
{
lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; 
v___x_6545_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6546_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6547_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6548_ = l_Lean_mkAppB(v___x_6547_, v___x_6546_, v___x_6545_);
return v___x_6548_;
}
}
static lean_object* _init_l_Lean_reflBoolTrue(void){
_start:
{
lean_object* v___x_6549_; 
v___x_6549_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__8, &l_Lean_reflBoolTrue___closed__8_once, _init_l_Lean_reflBoolTrue___closed__8);
return v___x_6549_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
v___x_6550_ = lean_box(0);
v___x_6551_ = ((lean_object*)(l_Lean_Expr_isBoolFalse___closed__2));
v___x_6552_ = l_Lean_Expr_const___override(v___x_6551_, v___x_6550_);
return v___x_6552_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; 
v___x_6553_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6554_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6555_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__4, &l_Lean_reflBoolTrue___closed__4_once, _init_l_Lean_reflBoolTrue___closed__4);
v___x_6556_ = l_Lean_mkAppB(v___x_6555_, v___x_6554_, v___x_6553_);
return v___x_6556_;
}
}
static lean_object* _init_l_Lean_reflBoolFalse(void){
_start:
{
lean_object* v___x_6557_; 
v___x_6557_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__1, &l_Lean_reflBoolFalse___closed__1_once, _init_l_Lean_reflBoolFalse___closed__1);
return v___x_6557_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__2(void){
_start:
{
lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6561_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natAddFn___closed__4, &l___private_Lean_Expr_0__Lean_natAddFn___closed__4_once, _init_l___private_Lean_Expr_0__Lean_natAddFn___closed__4);
v___x_6562_ = ((lean_object*)(l_Lean_eagerReflBoolTrue___closed__1));
v___x_6563_ = l_Lean_Expr_const___override(v___x_6562_, v___x_6561_);
return v___x_6563_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__3(void){
_start:
{
lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; 
v___x_6564_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__7, &l_Lean_reflBoolTrue___closed__7_once, _init_l_Lean_reflBoolTrue___closed__7);
v___x_6565_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6566_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6567_ = l_Lean_mkApp3(v___x_6566_, v___x_6565_, v___x_6564_, v___x_6564_);
return v___x_6567_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue___closed__4(void){
_start:
{
lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v___x_6568_ = l_Lean_reflBoolTrue;
v___x_6569_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__3, &l_Lean_eagerReflBoolTrue___closed__3_once, _init_l_Lean_eagerReflBoolTrue___closed__3);
v___x_6570_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6571_ = l_Lean_mkAppB(v___x_6570_, v___x_6569_, v___x_6568_);
return v___x_6571_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolTrue(void){
_start:
{
lean_object* v___x_6572_; 
v___x_6572_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__4, &l_Lean_eagerReflBoolTrue___closed__4_once, _init_l_Lean_eagerReflBoolTrue___closed__4);
return v___x_6572_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__0(void){
_start:
{
lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; 
v___x_6573_ = lean_obj_once(&l_Lean_reflBoolFalse___closed__0, &l_Lean_reflBoolFalse___closed__0_once, _init_l_Lean_reflBoolFalse___closed__0);
v___x_6574_ = lean_obj_once(&l_Lean_reflBoolTrue___closed__6, &l_Lean_reflBoolTrue___closed__6_once, _init_l_Lean_reflBoolTrue___closed__6);
v___x_6575_ = lean_obj_once(&l___private_Lean_Expr_0__Lean_natEqPred___closed__2, &l___private_Lean_Expr_0__Lean_natEqPred___closed__2_once, _init_l___private_Lean_Expr_0__Lean_natEqPred___closed__2);
v___x_6576_ = l_Lean_mkApp3(v___x_6575_, v___x_6574_, v___x_6573_, v___x_6573_);
return v___x_6576_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse___closed__1(void){
_start:
{
lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
v___x_6577_ = l_Lean_reflBoolFalse;
v___x_6578_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__0, &l_Lean_eagerReflBoolFalse___closed__0_once, _init_l_Lean_eagerReflBoolFalse___closed__0);
v___x_6579_ = lean_obj_once(&l_Lean_eagerReflBoolTrue___closed__2, &l_Lean_eagerReflBoolTrue___closed__2_once, _init_l_Lean_eagerReflBoolTrue___closed__2);
v___x_6580_ = l_Lean_mkAppB(v___x_6579_, v___x_6578_, v___x_6577_);
return v___x_6580_;
}
}
static lean_object* _init_l_Lean_eagerReflBoolFalse(void){
_start:
{
lean_object* v___x_6581_; 
v___x_6581_ = lean_obj_once(&l_Lean_eagerReflBoolFalse___closed__1, &l_Lean_eagerReflBoolFalse___closed__1_once, _init_l_Lean_eagerReflBoolFalse___closed__1);
return v___x_6581_;
}
}
static lean_object* _init_l_Lean_Expr_replaceFn___closed__2(void){
_start:
{
lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6584_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__1));
v___x_6585_ = lean_unsigned_to_nat(9u);
v___x_6586_ = lean_unsigned_to_nat(2508u);
v___x_6587_ = ((lean_object*)(l_Lean_Expr_replaceFn___closed__0));
v___x_6588_ = ((lean_object*)(l_Lean_Expr_appFn_x21___closed__0));
v___x_6589_ = l_mkPanicMessageWithDecl(v___x_6588_, v___x_6587_, v___x_6586_, v___x_6585_, v___x_6584_);
return v___x_6589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFn(lean_object* v_e_6590_, lean_object* v_declName_6591_){
_start:
{
switch(lean_obj_tag(v_e_6590_))
{
case 5:
{
lean_object* v_fn_6592_; lean_object* v_arg_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; 
v_fn_6592_ = lean_ctor_get(v_e_6590_, 0);
lean_inc_ref(v_fn_6592_);
v_arg_6593_ = lean_ctor_get(v_e_6590_, 1);
lean_inc_ref(v_arg_6593_);
lean_dec_ref_known(v_e_6590_, 2);
v___x_6594_ = l_Lean_Expr_replaceFn(v_fn_6592_, v_declName_6591_);
v___x_6595_ = l_Lean_Expr_app___override(v___x_6594_, v_arg_6593_);
return v___x_6595_;
}
case 4:
{
lean_object* v_us_6596_; lean_object* v___x_6597_; 
v_us_6596_ = lean_ctor_get(v_e_6590_, 1);
lean_inc(v_us_6596_);
lean_dec_ref_known(v_e_6590_, 2);
v___x_6597_ = l_Lean_Expr_const___override(v_declName_6591_, v_us_6596_);
return v___x_6597_;
}
default: 
{
lean_object* v___x_6598_; lean_object* v___x_6599_; 
lean_dec(v_declName_6591_);
lean_dec_ref(v_e_6590_);
v___x_6598_ = lean_obj_once(&l_Lean_Expr_replaceFn___closed__2, &l_Lean_Expr_replaceFn___closed__2_once, _init_l_Lean_Expr_replaceFn___closed__2);
v___x_6599_ = l_panic___at___00Lean_Expr_appFn_x21_spec__0(v___x_6598_);
return v___x_6599_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Level(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instLTLiteral = _init_l_Lean_instLTLiteral();
lean_mark_persistent(l_Lean_instLTLiteral);
l_Lean_instInhabitedBinderInfo_default = _init_l_Lean_instInhabitedBinderInfo_default();
l_Lean_instInhabitedBinderInfo = _init_l_Lean_instInhabitedBinderInfo();
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_instInhabitedData__1___aux__1 = _init_l_Lean_instInhabitedData__1___aux__1();
l_Lean_instInhabitedData__1 = _init_l_Lean_instInhabitedData__1();
l_Lean_instInhabitedFVarId_default = _init_l_Lean_instInhabitedFVarId_default();
lean_mark_persistent(l_Lean_instInhabitedFVarId_default);
l_Lean_instInhabitedFVarId = _init_l_Lean_instInhabitedFVarId();
lean_mark_persistent(l_Lean_instInhabitedFVarId);
l_Lean_instInhabitedFVarIdSet___aux__1 = _init_l_Lean_instInhabitedFVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedFVarIdSet___aux__1);
l_Lean_instInhabitedFVarIdSet = _init_l_Lean_instInhabitedFVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdSet);
l_Lean_instEmptyCollectionFVarIdSet___aux__1 = _init_l_Lean_instEmptyCollectionFVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdSet___aux__1);
l_Lean_instEmptyCollectionFVarIdSet = _init_l_Lean_instEmptyCollectionFVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdSet);
l_Lean_instInhabitedFVarIdHashSet___aux__1 = _init_l_Lean_instInhabitedFVarIdHashSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedFVarIdHashSet___aux__1);
l_Lean_instInhabitedFVarIdHashSet = _init_l_Lean_instInhabitedFVarIdHashSet();
lean_mark_persistent(l_Lean_instInhabitedFVarIdHashSet);
l_Lean_instEmptyCollectionFVarIdHashSet___aux__1 = _init_l_Lean_instEmptyCollectionFVarIdHashSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdHashSet___aux__1);
l_Lean_instEmptyCollectionFVarIdHashSet = _init_l_Lean_instEmptyCollectionFVarIdHashSet();
lean_mark_persistent(l_Lean_instEmptyCollectionFVarIdHashSet);
l_Lean_instInhabitedMVarId_default = _init_l_Lean_instInhabitedMVarId_default();
lean_mark_persistent(l_Lean_instInhabitedMVarId_default);
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instInhabitedMVarIdSet___aux__1 = _init_l_Lean_instInhabitedMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instInhabitedMVarIdSet___aux__1);
l_Lean_instInhabitedMVarIdSet = _init_l_Lean_instInhabitedMVarIdSet();
lean_mark_persistent(l_Lean_instInhabitedMVarIdSet);
l_Lean_instEmptyCollectionMVarIdSet___aux__1 = _init_l_Lean_instEmptyCollectionMVarIdSet___aux__1();
lean_mark_persistent(l_Lean_instEmptyCollectionMVarIdSet___aux__1);
l_Lean_instEmptyCollectionMVarIdSet = _init_l_Lean_instEmptyCollectionMVarIdSet();
lean_mark_persistent(l_Lean_instEmptyCollectionMVarIdSet);
l_Lean_instInhabitedExpr = _init_l_Lean_instInhabitedExpr();
lean_mark_persistent(l_Lean_instInhabitedExpr);
l_Lean_instInhabitedExprStructEq_default = _init_l_Lean_instInhabitedExprStructEq_default();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq_default);
l_Lean_instInhabitedExprStructEq = _init_l_Lean_instInhabitedExprStructEq();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq);
l_Lean_Nat_mkType = _init_l_Lean_Nat_mkType();
lean_mark_persistent(l_Lean_Nat_mkType);
l_Lean_Nat_mkInstAdd = _init_l_Lean_Nat_mkInstAdd();
lean_mark_persistent(l_Lean_Nat_mkInstAdd);
l_Lean_Nat_mkInstHAdd = _init_l_Lean_Nat_mkInstHAdd();
lean_mark_persistent(l_Lean_Nat_mkInstHAdd);
l_Lean_Nat_mkInstSub = _init_l_Lean_Nat_mkInstSub();
lean_mark_persistent(l_Lean_Nat_mkInstSub);
l_Lean_Nat_mkInstHSub = _init_l_Lean_Nat_mkInstHSub();
lean_mark_persistent(l_Lean_Nat_mkInstHSub);
l_Lean_Nat_mkInstMul = _init_l_Lean_Nat_mkInstMul();
lean_mark_persistent(l_Lean_Nat_mkInstMul);
l_Lean_Nat_mkInstHMul = _init_l_Lean_Nat_mkInstHMul();
lean_mark_persistent(l_Lean_Nat_mkInstHMul);
l_Lean_Nat_mkInstDiv = _init_l_Lean_Nat_mkInstDiv();
lean_mark_persistent(l_Lean_Nat_mkInstDiv);
l_Lean_Nat_mkInstHDiv = _init_l_Lean_Nat_mkInstHDiv();
lean_mark_persistent(l_Lean_Nat_mkInstHDiv);
l_Lean_Nat_mkInstMod = _init_l_Lean_Nat_mkInstMod();
lean_mark_persistent(l_Lean_Nat_mkInstMod);
l_Lean_Nat_mkInstHMod = _init_l_Lean_Nat_mkInstHMod();
lean_mark_persistent(l_Lean_Nat_mkInstHMod);
l_Lean_Nat_mkInstNatPow = _init_l_Lean_Nat_mkInstNatPow();
lean_mark_persistent(l_Lean_Nat_mkInstNatPow);
l_Lean_Nat_mkInstPow = _init_l_Lean_Nat_mkInstPow();
lean_mark_persistent(l_Lean_Nat_mkInstPow);
l_Lean_Nat_mkInstHPow = _init_l_Lean_Nat_mkInstHPow();
lean_mark_persistent(l_Lean_Nat_mkInstHPow);
l_Lean_Nat_mkInstLT = _init_l_Lean_Nat_mkInstLT();
lean_mark_persistent(l_Lean_Nat_mkInstLT);
l_Lean_Nat_mkInstLE = _init_l_Lean_Nat_mkInstLE();
lean_mark_persistent(l_Lean_Nat_mkInstLE);
l___private_Lean_Expr_0__Lean_natAddFn = _init_l___private_Lean_Expr_0__Lean_natAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natAddFn);
l___private_Lean_Expr_0__Lean_natSubFn = _init_l___private_Lean_Expr_0__Lean_natSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natSubFn);
l___private_Lean_Expr_0__Lean_natMulFn = _init_l___private_Lean_Expr_0__Lean_natMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natMulFn);
l___private_Lean_Expr_0__Lean_natPowFn = _init_l___private_Lean_Expr_0__Lean_natPowFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natPowFn);
l___private_Lean_Expr_0__Lean_natLEPred = _init_l___private_Lean_Expr_0__Lean_natLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natLEPred);
l___private_Lean_Expr_0__Lean_natEqPred = _init_l___private_Lean_Expr_0__Lean_natEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_natEqPred);
l___private_Lean_Expr_0__Lean_propEq = _init_l___private_Lean_Expr_0__Lean_propEq();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_propEq);
l_Lean_Int_mkType = _init_l_Lean_Int_mkType();
lean_mark_persistent(l_Lean_Int_mkType);
l_Lean_Int_mkInstNeg = _init_l_Lean_Int_mkInstNeg();
lean_mark_persistent(l_Lean_Int_mkInstNeg);
l_Lean_Int_mkInstAdd = _init_l_Lean_Int_mkInstAdd();
lean_mark_persistent(l_Lean_Int_mkInstAdd);
l_Lean_Int_mkInstHAdd = _init_l_Lean_Int_mkInstHAdd();
lean_mark_persistent(l_Lean_Int_mkInstHAdd);
l_Lean_Int_mkInstSub = _init_l_Lean_Int_mkInstSub();
lean_mark_persistent(l_Lean_Int_mkInstSub);
l_Lean_Int_mkInstHSub = _init_l_Lean_Int_mkInstHSub();
lean_mark_persistent(l_Lean_Int_mkInstHSub);
l_Lean_Int_mkInstMul = _init_l_Lean_Int_mkInstMul();
lean_mark_persistent(l_Lean_Int_mkInstMul);
l_Lean_Int_mkInstHMul = _init_l_Lean_Int_mkInstHMul();
lean_mark_persistent(l_Lean_Int_mkInstHMul);
l_Lean_Int_mkInstDiv = _init_l_Lean_Int_mkInstDiv();
lean_mark_persistent(l_Lean_Int_mkInstDiv);
l_Lean_Int_mkInstHDiv = _init_l_Lean_Int_mkInstHDiv();
lean_mark_persistent(l_Lean_Int_mkInstHDiv);
l_Lean_Int_mkInstMod = _init_l_Lean_Int_mkInstMod();
lean_mark_persistent(l_Lean_Int_mkInstMod);
l_Lean_Int_mkInstHMod = _init_l_Lean_Int_mkInstHMod();
lean_mark_persistent(l_Lean_Int_mkInstHMod);
l_Lean_Int_mkInstPow = _init_l_Lean_Int_mkInstPow();
lean_mark_persistent(l_Lean_Int_mkInstPow);
l_Lean_Int_mkInstPowNat = _init_l_Lean_Int_mkInstPowNat();
lean_mark_persistent(l_Lean_Int_mkInstPowNat);
l_Lean_Int_mkInstHPow = _init_l_Lean_Int_mkInstHPow();
lean_mark_persistent(l_Lean_Int_mkInstHPow);
l_Lean_Int_mkInstLT = _init_l_Lean_Int_mkInstLT();
lean_mark_persistent(l_Lean_Int_mkInstLT);
l_Lean_Int_mkInstLE = _init_l_Lean_Int_mkInstLE();
lean_mark_persistent(l_Lean_Int_mkInstLE);
l_Lean_Int_mkInstNatCast = _init_l_Lean_Int_mkInstNatCast();
lean_mark_persistent(l_Lean_Int_mkInstNatCast);
l___private_Lean_Expr_0__Lean_intNegFn = _init_l___private_Lean_Expr_0__Lean_intNegFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNegFn);
l___private_Lean_Expr_0__Lean_intAddFn = _init_l___private_Lean_Expr_0__Lean_intAddFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intAddFn);
l___private_Lean_Expr_0__Lean_intSubFn = _init_l___private_Lean_Expr_0__Lean_intSubFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intSubFn);
l___private_Lean_Expr_0__Lean_intMulFn = _init_l___private_Lean_Expr_0__Lean_intMulFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intMulFn);
l___private_Lean_Expr_0__Lean_intDivFn = _init_l___private_Lean_Expr_0__Lean_intDivFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intDivFn);
l___private_Lean_Expr_0__Lean_intModFn = _init_l___private_Lean_Expr_0__Lean_intModFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intModFn);
l___private_Lean_Expr_0__Lean_intPowNatFn = _init_l___private_Lean_Expr_0__Lean_intPowNatFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intPowNatFn);
l___private_Lean_Expr_0__Lean_intNatCastFn = _init_l___private_Lean_Expr_0__Lean_intNatCastFn();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intNatCastFn);
l___private_Lean_Expr_0__Lean_intLEPred = _init_l___private_Lean_Expr_0__Lean_intLEPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intLEPred);
l___private_Lean_Expr_0__Lean_intLTPred = _init_l___private_Lean_Expr_0__Lean_intLTPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intLTPred);
l___private_Lean_Expr_0__Lean_intEqPred = _init_l___private_Lean_Expr_0__Lean_intEqPred();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_intEqPred);
l_Lean_reflBoolTrue = _init_l_Lean_reflBoolTrue();
lean_mark_persistent(l_Lean_reflBoolTrue);
l_Lean_reflBoolFalse = _init_l_Lean_reflBoolFalse();
lean_mark_persistent(l_Lean_reflBoolFalse);
l_Lean_eagerReflBoolTrue = _init_l_Lean_eagerReflBoolTrue();
lean_mark_persistent(l_Lean_eagerReflBoolTrue);
l_Lean_eagerReflBoolFalse = _init_l_Lean_eagerReflBoolFalse();
lean_mark_persistent(l_Lean_eagerReflBoolFalse);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* initialize_Lean_Level(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Expr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Expr(builtin);
}
#ifdef __cplusplus
}
#endif

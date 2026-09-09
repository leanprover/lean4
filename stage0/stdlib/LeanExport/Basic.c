// Lean compiler output
// Module: LeanExport.Basic
// Imports: public import Lean public import Std.Data.HashMap.Basic
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_param___override(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_instReprDataValue_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_println___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_Lean_versionString;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "safe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__0;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__1;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__2;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__3;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__4;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__5;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__6;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__7;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__8;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__9;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__10;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__11;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__12;
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--ignore-missing"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__2___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--export-mdata"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__0___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--export-unsafe"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_LeanExport_initState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_LeanExport_initState___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_LeanExport_initState___closed__0 = (const lean_object*)&l_LeanExport_initState___closed__0_value;
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LeanExport.Basic"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpName"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "il"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpLevel"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "_private.LeanExport.Basic.0.LeanExport.removeMData"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanExport.dumpConstant"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "assertion violation: ((!recVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.2114.0 ).exportUnsafe)\n        "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "expected a `constantinfo.recinfo`."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "assertion violation: ((!ctorVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1873.0 ).exportUnsafe)\n          "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a `ConstantInfo.ctorInfo`."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_dumpExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__0;
static lean_once_cell_t l_LeanExport_dumpExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__1;
static const lean_string_object l_LeanExport_dumpExprAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ie"};
static const lean_object* l_LeanExport_dumpExprAux___closed__0 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_LeanExport_dumpExprAux___closed__1 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__1_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_LeanExport_dumpExprAux___closed__2 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__2_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_LeanExport_dumpExprAux___closed__3 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "us"};
static const lean_object* l_LeanExport_dumpExprAux___closed__4 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__4_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_LeanExport_dumpExprAux___closed__5 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__5_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l_LeanExport_dumpExprAux___closed__6 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__6_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_LeanExport_dumpExprAux___closed__7 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__7_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_LeanExport_dumpExprAux___closed__8 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__8_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_LeanExport_dumpExprAux___closed__9 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__9_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l_LeanExport_dumpExprAux___closed__10 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__10_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__11 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__11_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__12 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__12_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_LeanExport_dumpExprAux___closed__13 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__13_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nondep"};
static const lean_object* l_LeanExport_dumpExprAux___closed__14 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__14_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__15 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__15_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__16 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__16_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_LeanExport_dumpExprAux___closed__17 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__17_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_LeanExport_dumpExprAux___closed__18 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__18_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l_LeanExport_dumpExprAux___closed__19 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__19_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_LeanExport_dumpExprAux___closed__20 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__20_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeName"};
static const lean_object* l_LeanExport_dumpExprAux___closed__21 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__21_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_LeanExport_dumpExprAux___closed__22 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__22_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "struct"};
static const lean_object* l_LeanExport_dumpExprAux___closed__23 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__23_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "cannot export free variables or metavariables"};
static const lean_object* l_LeanExport_dumpExprAux___closed__25 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__25_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanExport.dumpExprAux"};
static const lean_object* l_LeanExport_dumpExprAux___closed__24 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__24_value;
static lean_once_cell_t l_LeanExport_dumpExprAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExprAux___closed__26;
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l_LeanExport_dumpConstant___closed__0 = (const lean_object*)&l_LeanExport_dumpConstant___closed__0_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l_LeanExport_dumpConstant___closed__1 = (const lean_object*)&l_LeanExport_dumpConstant___closed__1_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "recs"};
static const lean_object* l_LeanExport_dumpConstant___closed__2 = (const lean_object*)&l_LeanExport_dumpConstant___closed__2_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l_LeanExport_dumpConstant___closed__3 = (const lean_object*)&l_LeanExport_dumpConstant___closed__3_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_LeanExport_dumpConstant___closed__4 = (const lean_object*)&l_LeanExport_dumpConstant___closed__4_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hints"};
static const lean_object* l_LeanExport_dumpConstant___closed__5 = (const lean_object*)&l_LeanExport_dumpConstant___closed__5_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "safety"};
static const lean_object* l_LeanExport_dumpConstant___closed__6 = (const lean_object*)&l_LeanExport_dumpConstant___closed__6_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_LeanExport_dumpConstant___closed__7 = (const lean_object*)&l_LeanExport_dumpConstant___closed__7_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_LeanExport_dumpConstant___closed__8 = (const lean_object*)&l_LeanExport_dumpConstant___closed__8_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_LeanExport_dumpConstant___closed__9 = (const lean_object*)&l_LeanExport_dumpConstant___closed__9_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_LeanExport_dumpConstant___closed__10 = (const lean_object*)&l_LeanExport_dumpConstant___closed__10_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_LeanExport_dumpConstant___closed__15 = (const lean_object*)&l_LeanExport_dumpConstant___closed__15_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LeanExport_dumpConstant___closed__16 = (const lean_object*)&l_LeanExport_dumpConstant___closed__16_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_LeanExport_dumpConstant___closed__14 = (const lean_object*)&l_LeanExport_dumpConstant___closed__14_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value),((lean_object*)&l_LeanExport_dumpConstant___closed__16_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__17 = (const lean_object*)&l_LeanExport_dumpConstant___closed__17_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_LeanExport_dumpConstant___closed__12 = (const lean_object*)&l_LeanExport_dumpConstant___closed__12_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value_aux_0),((lean_object*)&l_LeanExport_dumpConstant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_LeanExport_dumpConstant___closed__13 = (const lean_object*)&l_LeanExport_dumpConstant___closed__13_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value),((lean_object*)&l_LeanExport_dumpConstant___closed__17_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__18 = (const lean_object*)&l_LeanExport_dumpConstant___closed__18_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_LeanExport_dumpConstant___closed__11 = (const lean_object*)&l_LeanExport_dumpConstant___closed__11_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__11_value),((lean_object*)&l_LeanExport_dumpConstant___closed__18_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__19 = (const lean_object*)&l_LeanExport_dumpConstant___closed__19_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Constant "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " not found in environment."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_LeanExport_dumpConstant___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LeanExport_dumpConstant___closed__20 = (const lean_object*)&l_LeanExport_dumpConstant___closed__20_value;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__21;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__22;
static const lean_closure_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 367, .m_capacity = 367, .m_length = 366, .m_data = "assertion violation: ctorVals.size == 0\n\n    /- We dump the constructor dependencies (which will not include the inductives in this block since we've\n    added the names to `visitedConstants`) before actually outputting anything in this inductive block to\n    ensure e.g. the `LT` in `Fin.mk` is dumped before this inductive block appears in the export file. -/\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 127, .m_capacity = 127, .m_length = 126, .m_data = "assertion violation: ((!val.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1797.0 ).exportUnsafe)\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "githash"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean4export"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "3.1.0"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "exporter"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
static lean_once_cell_t l_LeanExport_dumpMetadata___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpMetadata___redArg___closed__0;
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1));
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3));
return v___x_15_;
}
case 2:
{
lean_object* v___x_16_; 
v___x_16_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5));
return v___x_16_;
}
default: 
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7));
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object* v_x_18_){
_start:
{
uint8_t v_x_64__boxed_19_; lean_object* v_res_20_; 
v_x_64__boxed_19_ = lean_unbox(v_x_18_);
v_res_20_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_x_64__boxed_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object* v_x_28_){
_start:
{
switch(lean_obj_tag(v_x_28_))
{
case 0:
{
lean_object* v___x_29_; 
v___x_29_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1));
return v___x_29_;
}
case 1:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3));
return v___x_30_;
}
default: 
{
uint32_t v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_a_31_ = lean_ctor_get_uint32(v_x_28_, 0);
v___x_32_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4));
v___x_33_ = lean_uint32_to_nat(v_a_31_);
v___x_34_ = l_Lean_JsonNumber_fromNat(v___x_33_);
v___x_35_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_32_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_box(0);
v___x_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = l_Lean_Json_mkObj(v___x_38_);
lean_dec_ref_known(v___x_38_, 2);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_x_40_);
lean_dec(v_x_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t v_x_54_){
_start:
{
switch(v_x_54_)
{
case 0:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1));
return v___x_55_;
}
case 1:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3));
return v___x_56_;
}
case 2:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5));
return v___x_57_;
}
default: 
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7));
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object* v_x_59_){
_start:
{
uint8_t v_x_64__boxed_60_; lean_object* v_res_61_; 
v_x_64__boxed_60_ = lean_unbox(v_x_59_);
v_res_61_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_x_64__boxed_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t v_x_71_){
_start:
{
switch(v_x_71_)
{
case 0:
{
lean_object* v___x_72_; 
v___x_72_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1));
return v___x_72_;
}
case 1:
{
lean_object* v___x_73_; 
v___x_73_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3));
return v___x_73_;
}
default: 
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5));
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object* v_x_75_){
_start:
{
uint8_t v_x_49__boxed_76_; lean_object* v_res_77_; 
v_x_49__boxed_76_ = lean_unbox(v_x_75_);
v_res_77_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_x_49__boxed_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v___x_80_; 
v___x_80_ = l_List_reverse___redArg(v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_head_81_; lean_object* v_tail_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_106_; 
v_head_81_ = lean_ctor_get(v_a_78_, 0);
v_tail_82_ = lean_ctor_get(v_a_78_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_106_ == 0)
{
v___x_84_ = v_a_78_;
v_isShared_85_ = v_isSharedCheck_106_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_tail_82_);
lean_inc(v_head_81_);
lean_dec(v_a_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_106_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_105_; 
v_fst_86_ = lean_ctor_get(v_head_81_, 0);
v_snd_87_ = lean_ctor_get(v_head_81_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_head_81_);
if (v_isSharedCheck_105_ == 0)
{
v___x_89_ = v_head_81_;
v_isShared_90_ = v_isSharedCheck_105_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snd_87_);
lean_inc(v_fst_86_);
lean_dec(v_head_81_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_105_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_91_ = 1;
v___x_92_ = l_Lean_Name_toString(v_fst_86_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = l_Lean_instReprDataValue_repr(v_snd_87_, v___x_93_);
v___x_95_ = l_Std_Format_defWidth;
v___x_96_ = l_Std_Format_pretty(v___x_94_, v___x_95_, v___x_93_, v___x_93_);
v___x_97_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_97_);
lean_ctor_set(v___x_89_, 0, v___x_92_);
v___x_99_ = v___x_89_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_104_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_a_79_);
lean_ctor_set(v___x_84_, 0, v___x_99_);
v___x_101_ = v___x_84_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_79_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
v_a_78_ = v_tail_82_;
v_a_79_ = v___x_101_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object* v_kvs_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(v_kvs_107_, v___x_108_);
v___x_110_ = l_Lean_Json_mkObj(v___x_109_);
lean_dec(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object* v_a_111_, lean_object* v_b_112_, lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_dec(v_b_112_);
lean_dec(v_a_111_);
return v_x_113_;
}
else
{
lean_object* v_key_114_; lean_object* v_value_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_128_; 
v_key_114_ = lean_ctor_get(v_x_113_, 0);
v_value_115_ = lean_ctor_get(v_x_113_, 1);
v_tail_116_ = lean_ctor_get(v_x_113_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_128_ == 0)
{
v___x_118_ = v_x_113_;
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_value_115_);
lean_inc(v_key_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_128_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_name_eq(v_key_114_, v_a_111_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_111_, v_b_112_, v_tail_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_key_114_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_value_115_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
else
{
lean_object* v___x_126_; 
lean_dec(v_value_115_);
lean_dec(v_key_114_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_b_112_);
lean_ctor_set(v___x_118_, 0, v_a_111_);
v___x_126_ = v___x_118_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_b_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_tail_116_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
return v_x_129_;
}
else
{
lean_object* v_key_131_; lean_object* v_value_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_159_; 
v_key_131_ = lean_ctor_get(v_x_130_, 0);
v_value_132_ = lean_ctor_get(v_x_130_, 1);
v_tail_133_ = lean_ctor_get(v_x_130_, 2);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_159_ == 0)
{
v___x_135_ = v_x_130_;
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_value_132_);
lean_inc(v_key_131_);
lean_dec(v_x_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___y_139_; 
v___x_137_ = lean_array_get_size(v_x_129_);
if (lean_obj_tag(v_key_131_) == 0)
{
uint64_t v___x_157_; 
v___x_157_ = 1723ULL;
v___y_139_ = v___x_157_;
goto v___jp_138_;
}
else
{
uint64_t v_hash_158_; 
v_hash_158_ = lean_ctor_get_uint64(v_key_131_, sizeof(void*)*2);
v___y_139_ = v_hash_158_;
goto v___jp_138_;
}
v___jp_138_:
{
uint64_t v___x_140_; uint64_t v___x_141_; uint64_t v_fold_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_140_ = 32ULL;
v___x_141_ = lean_uint64_shift_right(v___y_139_, v___x_140_);
v_fold_142_ = lean_uint64_xor(v___y_139_, v___x_141_);
v___x_143_ = 16ULL;
v___x_144_ = lean_uint64_shift_right(v_fold_142_, v___x_143_);
v___x_145_ = lean_uint64_xor(v_fold_142_, v___x_144_);
v___x_146_ = lean_uint64_to_usize(v___x_145_);
v___x_147_ = lean_usize_of_nat(v___x_137_);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_sub(v___x_147_, v___x_148_);
v___x_150_ = lean_usize_land(v___x_146_, v___x_149_);
v___x_151_ = lean_array_uget_borrowed(v_x_129_, v___x_150_);
lean_inc(v___x_151_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 2, v___x_151_);
v___x_153_ = v___x_135_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_key_131_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_value_132_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v___x_151_);
v___x_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_array_uset(v_x_129_, v___x_150_, v___x_153_);
v_x_129_ = v___x_154_;
v_x_130_ = v_tail_133_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object* v_i_160_, lean_object* v_source_161_, lean_object* v_target_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_source_161_);
v___x_164_ = lean_nat_dec_lt(v_i_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_source_161_);
lean_dec(v_i_160_);
return v_target_162_;
}
else
{
lean_object* v_es_165_; lean_object* v___x_166_; lean_object* v_source_167_; lean_object* v_target_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_es_165_ = lean_array_fget(v_source_161_, v_i_160_);
v___x_166_ = lean_box(0);
v_source_167_ = lean_array_fset(v_source_161_, v_i_160_, v___x_166_);
v_target_168_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_target_162_, v_es_165_);
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_160_, v___x_169_);
lean_dec(v_i_160_);
v_i_160_ = v___x_170_;
v_source_161_ = v_source_167_;
v_target_162_ = v_target_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object* v_data_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_nbuckets_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_173_ = lean_array_get_size(v_data_172_);
v___x_174_ = lean_unsigned_to_nat(2u);
v_nbuckets_175_ = lean_nat_mul(v___x_173_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_box(0);
v___x_178_ = lean_mk_array(v_nbuckets_175_, v___x_177_);
v___x_179_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v___x_176_, v_data_172_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
else
{
lean_object* v_key_183_; lean_object* v_tail_184_; uint8_t v___x_185_; 
v_key_183_ = lean_ctor_get(v_x_181_, 0);
v_tail_184_ = lean_ctor_get(v_x_181_, 2);
v___x_185_ = lean_name_eq(v_key_183_, v_a_180_);
if (v___x_185_ == 0)
{
v_x_181_ = v_tail_184_;
goto _start;
}
else
{
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_187_, lean_object* v_x_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_187_, v_x_188_);
lean_dec(v_x_188_);
lean_dec(v_a_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object* v_m_191_, lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v_size_194_; lean_object* v_buckets_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_241_; 
v_size_194_ = lean_ctor_get(v_m_191_, 0);
v_buckets_195_ = lean_ctor_get(v_m_191_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_m_191_);
if (v_isSharedCheck_241_ == 0)
{
v___x_197_ = v_m_191_;
v_isShared_198_ = v_isSharedCheck_241_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_buckets_195_);
lean_inc(v_size_194_);
lean_dec(v_m_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_241_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; uint64_t v___y_201_; 
v___x_199_ = lean_array_get_size(v_buckets_195_);
if (lean_obj_tag(v_a_192_) == 0)
{
uint64_t v___x_239_; 
v___x_239_ = 1723ULL;
v___y_201_ = v___x_239_;
goto v___jp_200_;
}
else
{
uint64_t v_hash_240_; 
v_hash_240_ = lean_ctor_get_uint64(v_a_192_, sizeof(void*)*2);
v___y_201_ = v_hash_240_;
goto v___jp_200_;
}
v___jp_200_:
{
uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v_fold_204_; uint64_t v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; lean_object* v_bkt_213_; uint8_t v___x_214_; 
v___x_202_ = 32ULL;
v___x_203_ = lean_uint64_shift_right(v___y_201_, v___x_202_);
v_fold_204_ = lean_uint64_xor(v___y_201_, v___x_203_);
v___x_205_ = 16ULL;
v___x_206_ = lean_uint64_shift_right(v_fold_204_, v___x_205_);
v___x_207_ = lean_uint64_xor(v_fold_204_, v___x_206_);
v___x_208_ = lean_uint64_to_usize(v___x_207_);
v___x_209_ = lean_usize_of_nat(v___x_199_);
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_sub(v___x_209_, v___x_210_);
v___x_212_ = lean_usize_land(v___x_208_, v___x_211_);
v_bkt_213_ = lean_array_uget_borrowed(v_buckets_195_, v___x_212_);
v___x_214_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_192_, v_bkt_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v_size_x27_216_; lean_object* v___x_217_; lean_object* v_buckets_x27_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v_size_x27_216_ = lean_nat_add(v_size_194_, v___x_215_);
lean_dec(v_size_194_);
lean_inc(v_bkt_213_);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v_a_192_);
lean_ctor_set(v___x_217_, 1, v_b_193_);
lean_ctor_set(v___x_217_, 2, v_bkt_213_);
v_buckets_x27_218_ = lean_array_uset(v_buckets_195_, v___x_212_, v___x_217_);
v___x_219_ = lean_unsigned_to_nat(4u);
v___x_220_ = lean_nat_mul(v_size_x27_216_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(3u);
v___x_222_ = lean_nat_div(v___x_220_, v___x_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_array_get_size(v_buckets_x27_218_);
v___x_224_ = lean_nat_dec_le(v___x_222_, v___x_223_);
lean_dec(v___x_222_);
if (v___x_224_ == 0)
{
lean_object* v_val_225_; lean_object* v___x_227_; 
v_val_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_buckets_x27_218_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v_val_225_);
lean_ctor_set(v___x_197_, 0, v_size_x27_216_);
v___x_227_ = v___x_197_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_size_x27_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_val_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
else
{
lean_object* v___x_230_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v_buckets_x27_218_);
lean_ctor_set(v___x_197_, 0, v_size_x27_216_);
v___x_230_ = v___x_197_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_size_x27_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_buckets_x27_218_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v___x_232_; lean_object* v_buckets_x27_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
lean_inc(v_bkt_213_);
v___x_232_ = lean_box(0);
v_buckets_x27_233_ = lean_array_uset(v_buckets_195_, v___x_212_, v___x_232_);
v___x_234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_192_, v_b_193_, v_bkt_213_);
v___x_235_ = lean_array_uset(v_buckets_x27_233_, v___x_212_, v___x_234_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_235_);
v___x_237_ = v___x_197_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_194_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object* v_a_242_, lean_object* v_b_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_dec(v_b_243_);
lean_dec(v_a_242_);
return v_x_244_;
}
else
{
lean_object* v_key_245_; lean_object* v_value_246_; lean_object* v_tail_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_259_; 
v_key_245_ = lean_ctor_get(v_x_244_, 0);
v_value_246_ = lean_ctor_get(v_x_244_, 1);
v_tail_247_ = lean_ctor_get(v_x_244_, 2);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_259_ == 0)
{
v___x_249_ = v_x_244_;
v_isShared_250_ = v_isSharedCheck_259_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_tail_247_);
lean_inc(v_value_246_);
lean_inc(v_key_245_);
lean_dec(v_x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_259_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
uint8_t v___x_251_; 
v___x_251_ = lean_level_eq(v_key_245_, v_a_242_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_242_, v_b_243_, v_tail_247_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 2, v___x_252_);
v___x_254_ = v___x_249_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_key_245_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_value_246_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
lean_object* v___x_257_; 
lean_dec(v_value_246_);
lean_dec(v_key_245_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v_b_243_);
lean_ctor_set(v___x_249_, 0, v_a_242_);
v___x_257_ = v___x_249_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_242_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_b_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_tail_247_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
return v_x_260_;
}
else
{
lean_object* v_key_262_; lean_object* v_value_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_287_; 
v_key_262_ = lean_ctor_get(v_x_261_, 0);
v_value_263_ = lean_ctor_get(v_x_261_, 1);
v_tail_264_ = lean_ctor_get(v_x_261_, 2);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_287_ == 0)
{
v___x_266_ = v_x_261_;
v_isShared_267_ = v_isSharedCheck_287_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_value_263_);
lean_inc(v_key_262_);
lean_dec(v_x_261_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_287_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v_fold_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_268_ = lean_array_get_size(v_x_260_);
v___x_269_ = l_Lean_Level_hash(v_key_262_);
v___x_270_ = 32ULL;
v___x_271_ = lean_uint64_shift_right(v___x_269_, v___x_270_);
v_fold_272_ = lean_uint64_xor(v___x_269_, v___x_271_);
v___x_273_ = 16ULL;
v___x_274_ = lean_uint64_shift_right(v_fold_272_, v___x_273_);
v___x_275_ = lean_uint64_xor(v_fold_272_, v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = lean_usize_of_nat(v___x_268_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v___x_277_, v___x_278_);
v___x_280_ = lean_usize_land(v___x_276_, v___x_279_);
v___x_281_ = lean_array_uget_borrowed(v_x_260_, v___x_280_);
lean_inc(v___x_281_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v___x_281_);
v___x_283_ = v___x_266_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_key_262_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_value_263_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v___x_281_);
v___x_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_uset(v_x_260_, v___x_280_, v___x_283_);
v_x_260_ = v___x_284_;
v_x_261_ = v_tail_264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object* v_i_288_, lean_object* v_source_289_, lean_object* v_target_290_){
_start:
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_array_get_size(v_source_289_);
v___x_292_ = lean_nat_dec_lt(v_i_288_, v___x_291_);
if (v___x_292_ == 0)
{
lean_dec_ref(v_source_289_);
lean_dec(v_i_288_);
return v_target_290_;
}
else
{
lean_object* v_es_293_; lean_object* v___x_294_; lean_object* v_source_295_; lean_object* v_target_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_es_293_ = lean_array_fget(v_source_289_, v_i_288_);
v___x_294_ = lean_box(0);
v_source_295_ = lean_array_fset(v_source_289_, v_i_288_, v___x_294_);
v_target_296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_target_290_, v_es_293_);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_i_288_, v___x_297_);
lean_dec(v_i_288_);
v_i_288_ = v___x_298_;
v_source_289_ = v_source_295_;
v_target_290_ = v_target_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object* v_data_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_nbuckets_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_301_ = lean_array_get_size(v_data_300_);
v___x_302_ = lean_unsigned_to_nat(2u);
v_nbuckets_303_ = lean_nat_mul(v___x_301_, v___x_302_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_box(0);
v___x_306_ = lean_mk_array(v_nbuckets_303_, v___x_305_);
v___x_307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v___x_304_, v_data_300_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
else
{
lean_object* v_key_311_; lean_object* v_tail_312_; uint8_t v___x_313_; 
v_key_311_ = lean_ctor_get(v_x_309_, 0);
v_tail_312_ = lean_ctor_get(v_x_309_, 2);
v___x_313_ = lean_level_eq(v_key_311_, v_a_308_);
if (v___x_313_ == 0)
{
v_x_309_ = v_tail_312_;
goto _start;
}
else
{
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_315_, v_x_316_);
lean_dec(v_x_316_);
lean_dec(v_a_315_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object* v_m_319_, lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_size_322_; lean_object* v_buckets_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_366_; 
v_size_322_ = lean_ctor_get(v_m_319_, 0);
v_buckets_323_ = lean_ctor_get(v_m_319_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_m_319_);
if (v_isSharedCheck_366_ == 0)
{
v___x_325_ = v_m_319_;
v_isShared_326_ = v_isSharedCheck_366_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_buckets_323_);
lean_inc(v_size_322_);
lean_dec(v_m_319_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_366_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v_fold_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; size_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v_bkt_340_; uint8_t v___x_341_; 
v___x_327_ = lean_array_get_size(v_buckets_323_);
v___x_328_ = l_Lean_Level_hash(v_a_320_);
v___x_329_ = 32ULL;
v___x_330_ = lean_uint64_shift_right(v___x_328_, v___x_329_);
v_fold_331_ = lean_uint64_xor(v___x_328_, v___x_330_);
v___x_332_ = 16ULL;
v___x_333_ = lean_uint64_shift_right(v_fold_331_, v___x_332_);
v___x_334_ = lean_uint64_xor(v_fold_331_, v___x_333_);
v___x_335_ = lean_uint64_to_usize(v___x_334_);
v___x_336_ = lean_usize_of_nat(v___x_327_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_sub(v___x_336_, v___x_337_);
v___x_339_ = lean_usize_land(v___x_335_, v___x_338_);
v_bkt_340_ = lean_array_uget_borrowed(v_buckets_323_, v___x_339_);
v___x_341_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_320_, v_bkt_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v_size_x27_343_; lean_object* v___x_344_; lean_object* v_buckets_x27_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v_size_x27_343_ = lean_nat_add(v_size_322_, v___x_342_);
lean_dec(v_size_322_);
lean_inc(v_bkt_340_);
v___x_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_344_, 0, v_a_320_);
lean_ctor_set(v___x_344_, 1, v_b_321_);
lean_ctor_set(v___x_344_, 2, v_bkt_340_);
v_buckets_x27_345_ = lean_array_uset(v_buckets_323_, v___x_339_, v___x_344_);
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = lean_nat_mul(v_size_x27_343_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(3u);
v___x_349_ = lean_nat_div(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_array_get_size(v_buckets_x27_345_);
v___x_351_ = lean_nat_dec_le(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
if (v___x_351_ == 0)
{
lean_object* v_val_352_; lean_object* v___x_354_; 
v_val_352_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_buckets_x27_345_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_val_352_);
lean_ctor_set(v___x_325_, 0, v_size_x27_343_);
v___x_354_ = v___x_325_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_size_x27_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_val_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
else
{
lean_object* v___x_357_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_buckets_x27_345_);
lean_ctor_set(v___x_325_, 0, v_size_x27_343_);
v___x_357_ = v___x_325_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_size_x27_343_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_buckets_x27_345_);
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
lean_object* v___x_359_; lean_object* v_buckets_x27_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_bkt_340_);
v___x_359_ = lean_box(0);
v_buckets_x27_360_ = lean_array_uset(v_buckets_323_, v___x_339_, v___x_359_);
v___x_361_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_320_, v_b_321_, v_bkt_340_);
v___x_362_ = lean_array_uset(v_buckets_x27_360_, v___x_339_, v___x_361_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_362_);
v___x_364_ = v___x_325_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_322_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_box(0);
v___x_368_ = lean_unsigned_to_nat(524288u);
v___x_369_ = lean_mk_array(v___x_368_, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__0, &l_LeanExport_M_run___redArg___closed__0_once, _init_l_LeanExport_M_run___redArg___closed__0);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_box(0);
v___x_375_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__1, &l_LeanExport_M_run___redArg___closed__1_once, _init_l_LeanExport_M_run___redArg___closed__1);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v___x_375_, v___x_374_, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_box(0);
v___x_378_ = lean_unsigned_to_nat(2048u);
v___x_379_ = lean_mk_array(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__3, &l_LeanExport_M_run___redArg___closed__3_once, _init_l_LeanExport_M_run___redArg___closed__3);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_box(0);
v___x_385_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__4, &l_LeanExport_M_run___redArg___closed__4_once, _init_l_LeanExport_M_run___redArg___closed__4);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v___x_385_, v___x_384_, v___x_383_);
return v___x_386_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__6(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_box(0);
v___x_388_ = lean_unsigned_to_nat(16777216u);
v___x_389_ = lean_mk_array(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__6, &l_LeanExport_M_run___redArg___closed__6_once, _init_l_LeanExport_M_run___redArg___closed__6);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
return v___x_392_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_box(0);
v___x_394_ = lean_unsigned_to_nat(16u);
v___x_395_ = lean_mk_array(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__8, &l_LeanExport_M_run___redArg___closed__8_once, _init_l_LeanExport_M_run___redArg___closed__8);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__10(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
v___x_400_ = lean_unsigned_to_nat(262144u);
v___x_401_ = lean_mk_array(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__11(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__10, &l_LeanExport_M_run___redArg___closed__10_once, _init_l_LeanExport_M_run___redArg___closed__10);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__12(void){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_405_ = lean_box(1);
v___x_406_ = 0;
v___x_407_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__11, &l_LeanExport_M_run___redArg___closed__11_once, _init_l_LeanExport_M_run___redArg___closed__11);
v___x_408_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__9, &l_LeanExport_M_run___redArg___closed__9_once, _init_l_LeanExport_M_run___redArg___closed__9);
v___x_409_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__7, &l_LeanExport_M_run___redArg___closed__7_once, _init_l_LeanExport_M_run___redArg___closed__7);
v___x_410_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__5, &l_LeanExport_M_run___redArg___closed__5_once, _init_l_LeanExport_M_run___redArg___closed__5);
v___x_411_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__2, &l_LeanExport_M_run___redArg___closed__2_once, _init_l_LeanExport_M_run___redArg___closed__2);
v___x_412_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
lean_ctor_set(v___x_412_, 3, v___x_408_);
lean_ctor_set(v___x_412_, 4, v___x_407_);
lean_ctor_set(v___x_412_, 5, v___x_405_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*6, v___x_406_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*6 + 1, v___x_406_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*6 + 2, v___x_406_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object* v_env_413_, lean_object* v_act_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__12, &l_LeanExport_M_run___redArg___closed__12_once, _init_l_LeanExport_M_run___redArg___closed__12);
v___x_417_ = lean_apply_3(v_act_414_, v_env_413_, v___x_416_, lean_box(0));
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_fst_422_; lean_object* v___x_424_; 
v_fst_422_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_fst_422_);
lean_dec(v_a_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_fst_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_fst_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_417_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object* v_env_435_, lean_object* v_act_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_LeanExport_M_run___redArg(v_env_435_, v_act_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object* v_00_u03b1_439_, lean_object* v_env_440_, lean_object* v_act_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_LeanExport_M_run___redArg(v_env_440_, v_act_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object* v_00_u03b1_444_, lean_object* v_env_445_, lean_object* v_act_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_LeanExport_M_run(v_00_u03b1_444_, v_env_445_, v_act_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object* v_00_u03b2_449_, lean_object* v_m_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_m_450_, v_a_451_, v_b_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object* v_00_u03b2_454_, lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_m_455_, v_a_456_, v_b_457_);
return v___x_458_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(v_00_u03b2_463_, v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_a_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object* v_00_u03b2_468_, lean_object* v_data_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_data_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object* v_00_u03b2_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_472_, v_b_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object* v_00_u03b2_476_, lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object* v_00_u03b2_480_, lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(v_00_u03b2_480_, v_a_481_, v_x_482_);
lean_dec(v_x_482_);
lean_dec(v_a_481_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object* v_00_u03b2_485_, lean_object* v_data_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_data_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object* v_00_u03b2_488_, lean_object* v_a_489_, lean_object* v_b_490_, lean_object* v_x_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_489_, v_b_490_, v_x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_493_, lean_object* v_i_494_, lean_object* v_source_495_, lean_object* v_target_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v_i_494_, v_source_495_, v_target_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_498_, lean_object* v_i_499_, lean_object* v_source_500_, lean_object* v_target_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v_i_499_, v_source_500_, v_target_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_x_504_, v_x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_x_508_, v_x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object* v_val_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_toConstantVal_513_; lean_object* v_name_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_toConstantVal_513_ = lean_ctor_get(v_val_511_, 0);
lean_inc_ref(v_toConstantVal_513_);
lean_dec_ref(v_val_511_);
v_name_514_ = lean_ctor_get(v_toConstantVal_513_, 0);
lean_inc(v_name_514_);
lean_dec_ref(v_toConstantVal_513_);
v___x_515_ = l_Lean_NameSet_empty;
v___x_516_ = l_Lean_NameSet_insert(v___x_515_, v_name_514_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
else
{
lean_object* v_toConstantVal_518_; lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v_toConstantVal_518_ = lean_ctor_get(v_val_511_, 0);
lean_inc_ref(v_toConstantVal_518_);
lean_dec_ref(v_val_511_);
v_val_519_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_528_ == 0)
{
v___x_521_ = v_x_512_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v_x_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_name_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v_name_523_ = lean_ctor_get(v_toConstantVal_518_, 0);
lean_inc(v_name_523_);
lean_dec_ref(v_toConstantVal_518_);
v___x_524_ = l_Lean_NameSet_insert(v_val_519_, v_name_523_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object* v_val_529_, lean_object* v_k_530_, lean_object* v_t_531_){
_start:
{
if (lean_obj_tag(v_t_531_) == 0)
{
lean_object* v_size_532_; lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v_l_535_; lean_object* v_r_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_551_; 
v_size_532_ = lean_ctor_get(v_t_531_, 0);
v_k_533_ = lean_ctor_get(v_t_531_, 1);
v_v_534_ = lean_ctor_get(v_t_531_, 2);
v_l_535_ = lean_ctor_get(v_t_531_, 3);
v_r_536_ = lean_ctor_get(v_t_531_, 4);
v_isSharedCheck_551_ = !lean_is_exclusive(v_t_531_);
if (v_isSharedCheck_551_ == 0)
{
v___x_538_ = v_t_531_;
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_r_536_);
lean_inc(v_l_535_);
lean_inc(v_v_534_);
lean_inc(v_k_533_);
lean_inc(v_size_532_);
lean_dec(v_t_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___x_540_; 
v___x_540_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_530_, v_k_533_);
switch(v___x_540_)
{
case 0:
{
lean_object* v_impl_541_; lean_object* v___x_542_; 
lean_del_object(v___x_538_);
lean_dec(v_size_532_);
v_impl_541_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_529_, v_k_530_, v_l_535_);
v___x_542_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_533_, v_v_534_, v_impl_541_, v_r_536_);
return v___x_542_;
}
case 1:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_val_545_; lean_object* v___x_547_; 
lean_dec(v_k_533_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_v_534_);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_529_, v___x_543_);
v_val_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_545_);
lean_dec(v___x_544_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 2, v_val_545_);
lean_ctor_set(v___x_538_, 1, v_k_530_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_size_532_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_k_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_val_545_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_l_535_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_r_536_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
default: 
{
lean_object* v_impl_549_; lean_object* v___x_550_; 
lean_del_object(v___x_538_);
lean_dec(v_size_532_);
v_impl_549_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_529_, v_k_530_, v_r_536_);
v___x_550_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_533_, v_v_534_, v_l_535_, v_impl_549_);
return v___x_550_;
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_val_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_552_ = lean_box(0);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_529_, v___x_552_);
v_val_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v_k_530_);
lean_ctor_set(v___x_556_, 2, v_val_554_);
lean_ctor_set(v___x_556_, 3, v_t_531_);
lean_ctor_set(v___x_556_, 4, v_t_531_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object* v_val_557_, lean_object* v_as_x27_558_, lean_object* v_b_559_, lean_object* v___y_560_){
_start:
{
if (lean_obj_tag(v_as_x27_558_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v_val_557_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_b_559_);
lean_ctor_set(v___x_562_, 1, v___y_560_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
else
{
lean_object* v_head_564_; lean_object* v_tail_565_; lean_object* v___x_566_; 
v_head_564_ = lean_ctor_get(v_as_x27_558_, 0);
v_tail_565_ = lean_ctor_get(v_as_x27_558_, 1);
lean_inc(v_head_564_);
lean_inc_ref(v_val_557_);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_557_, v_head_564_, v_b_559_);
v_as_x27_558_ = v_tail_565_;
v_b_559_ = v___x_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object* v_val_568_, lean_object* v_as_x27_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_568_, v_as_x27_569_, v_b_570_, v___y_571_);
lean_dec(v_as_x27_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object* v_x_574_, lean_object* v_y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_a_581_; lean_object* v_snd_582_; 
if (lean_obj_tag(v_y_575_) == 7)
{
lean_object* v_val_588_; lean_object* v_all_589_; lean_object* v___x_590_; lean_object* v_a_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; 
v_val_588_ = lean_ctor_get(v_y_575_, 0);
lean_inc_ref(v_val_588_);
lean_dec_ref_known(v_y_575_, 1);
v_all_589_ = lean_ctor_get(v_val_588_, 1);
lean_inc(v_all_589_);
v___x_590_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_588_, v_all_589_, v___y_576_, v___y_578_);
lean_dec(v_all_589_);
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
v_fst_592_ = lean_ctor_get(v_a_591_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_a_591_, 1);
lean_inc(v_snd_593_);
lean_dec(v_a_591_);
v_a_581_ = v_fst_592_;
v_snd_582_ = v_snd_593_;
goto v___jp_580_;
}
else
{
lean_dec_ref(v_y_575_);
v_a_581_ = v___y_576_;
v_snd_582_ = v___y_578_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_a_581_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_snd_582_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object* v_x_594_, lean_object* v_y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_LeanExport_initState___lam__0(v_x_594_, v_y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v_x_594_);
return v_res_600_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
uint8_t v___x_603_; 
v___x_603_ = 0;
return v___x_603_;
}
else
{
lean_object* v_head_604_; lean_object* v_tail_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_head_604_ = lean_ctor_get(v_x_602_, 0);
v_tail_605_ = lean_ctor_get(v_x_602_, 1);
v___x_606_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__2___closed__0));
v___x_607_ = lean_string_dec_eq(v_head_604_, v___x_606_);
if (v___x_607_ == 0)
{
v_x_602_ = v_tail_605_;
goto _start;
}
else
{
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_List_any___at___00LeanExport_initState_spec__2(v_x_609_);
lean_dec(v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 0;
return v___x_614_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_head_615_ = lean_ctor_get(v_x_613_, 0);
v_tail_616_ = lean_ctor_get(v_x_613_, 1);
v___x_617_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__0___closed__0));
v___x_618_ = lean_string_dec_eq(v_head_615_, v___x_617_);
if (v___x_618_ == 0)
{
v_x_613_ = v_tail_616_;
goto _start;
}
else
{
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object* v_x_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_List_any___at___00LeanExport_initState_spec__0(v_x_620_);
lean_dec(v_x_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_head_626_ = lean_ctor_get(v_x_624_, 0);
v_tail_627_ = lean_ctor_get(v_x_624_, 1);
v___x_628_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_629_ = lean_string_dec_eq(v_head_626_, v___x_628_);
if (v___x_629_ == 0)
{
v_x_624_ = v_tail_627_;
goto _start;
}
else
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_631_);
lean_dec(v_x_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_f_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v_f_634_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_x_635_);
lean_ctor_set(v___x_641_, 1, v___y_637_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___y_639_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_key_645_; lean_object* v_value_646_; lean_object* v_tail_647_; lean_object* v___x_648_; 
v_key_645_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_key_645_);
v_value_646_ = lean_ctor_get(v_x_636_, 1);
lean_inc(v_value_646_);
v_tail_647_ = lean_ctor_get(v_x_636_, 2);
lean_inc(v_tail_647_);
lean_dec_ref_known(v_x_636_, 3);
lean_inc_ref(v_f_634_);
lean_inc_ref(v___y_638_);
v___x_648_ = lean_apply_6(v_f_634_, v_key_645_, v_value_646_, v___y_637_, v___y_638_, v___y_639_, lean_box(0));
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v_fst_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
v_fst_650_ = lean_ctor_get(v_a_649_, 0);
if (lean_obj_tag(v_fst_650_) == 0)
{
lean_dec(v_a_649_);
lean_dec(v_tail_647_);
lean_dec_ref(v_f_634_);
return v___x_648_;
}
else
{
lean_object* v_a_651_; lean_object* v_snd_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; 
lean_dec_ref_known(v___x_648_, 1);
v_a_651_ = lean_ctor_get(v_fst_650_, 0);
lean_inc(v_a_651_);
v_snd_652_ = lean_ctor_get(v_a_649_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_649_);
v_fst_653_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_651_);
v_x_635_ = v_fst_653_;
v_x_636_ = v_tail_647_;
v___y_637_ = v_snd_654_;
v___y_639_ = v_snd_652_;
goto _start;
}
}
else
{
lean_dec(v_tail_647_);
lean_dec_ref(v_f_634_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_f_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_656_, v_x_657_, v_x_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object* v_f_664_, lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_, lean_object* v_b_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
v___x_675_ = lean_box(0);
lean_inc(v___x_674_);
lean_inc_ref(v_f_664_);
v___x_676_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_664_, v___x_675_, v___x_674_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v_fst_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
v_fst_678_ = lean_ctor_get(v_a_677_, 0);
if (lean_obj_tag(v_fst_678_) == 0)
{
lean_dec(v_a_677_);
lean_dec_ref(v_f_664_);
return v___x_676_;
}
else
{
lean_object* v_a_679_; lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; size_t v___x_683_; size_t v___x_684_; 
lean_dec_ref_known(v___x_676_, 1);
v_a_679_ = lean_ctor_get(v_fst_678_, 0);
lean_inc(v_a_679_);
v_snd_680_ = lean_ctor_get(v_a_677_, 1);
lean_inc(v_snd_680_);
lean_dec(v_a_677_);
v_fst_681_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_fst_681_);
v_snd_682_ = lean_ctor_get(v_a_679_, 1);
lean_inc(v_snd_682_);
lean_dec(v_a_679_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = lean_usize_add(v_i_666_, v___x_683_);
v_i_666_ = v___x_684_;
v_b_668_ = v_fst_681_;
v___y_669_ = v_snd_682_;
v___y_671_ = v_snd_680_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_664_);
return v___x_676_;
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v_f_664_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_b_668_);
lean_ctor_set(v___x_686_, 1, v___y_669_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___y_671_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object* v_f_690_, lean_object* v_as_691_, lean_object* v_i_692_, lean_object* v_stop_693_, lean_object* v_b_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_i_boxed_699_; size_t v_stop_boxed_700_; lean_object* v_res_701_; 
v_i_boxed_699_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_stop_boxed_700_ = lean_unbox_usize(v_stop_693_);
lean_dec(v_stop_693_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_690_, v_as_691_, v_i_boxed_699_, v_stop_boxed_700_, v_b_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_as_691_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
lean_inc_ref(v___y_707_);
v___x_710_ = lean_apply_6(v_f_702_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object* v_f_720_, lean_object* v_keys_721_, lean_object* v_vals_722_, lean_object* v_i_723_, lean_object* v_acc_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_get_size(v_keys_721_);
v___x_730_ = lean_nat_dec_lt(v_i_723_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec(v_i_723_);
lean_dec_ref(v_f_720_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_acc_724_);
lean_ctor_set(v___x_731_, 1, v___y_725_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___y_727_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v___x_737_; 
v_k_735_ = lean_array_fget_borrowed(v_keys_721_, v_i_723_);
v_v_736_ = lean_array_fget_borrowed(v_vals_722_, v_i_723_);
lean_inc_ref(v_f_720_);
lean_inc_ref(v___y_726_);
lean_inc(v_v_736_);
lean_inc(v_k_735_);
v___x_737_ = lean_apply_7(v_f_720_, v_acc_724_, v_k_735_, v_v_736_, v___y_725_, v___y_726_, v___y_727_, lean_box(0));
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v_fst_739_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
v_fst_739_ = lean_ctor_get(v_a_738_, 0);
if (lean_obj_tag(v_fst_739_) == 0)
{
lean_dec(v_a_738_);
lean_dec(v_i_723_);
lean_dec_ref(v_f_720_);
return v___x_737_;
}
else
{
lean_object* v_a_740_; lean_object* v_snd_741_; lean_object* v_fst_742_; lean_object* v_snd_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec_ref_known(v___x_737_, 1);
v_a_740_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_a_740_);
v_snd_741_ = lean_ctor_get(v_a_738_, 1);
lean_inc(v_snd_741_);
lean_dec(v_a_738_);
v_fst_742_ = lean_ctor_get(v_a_740_, 0);
lean_inc(v_fst_742_);
v_snd_743_ = lean_ctor_get(v_a_740_, 1);
lean_inc(v_snd_743_);
lean_dec(v_a_740_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_i_723_, v___x_744_);
lean_dec(v_i_723_);
v_i_723_ = v___x_745_;
v_acc_724_ = v_fst_742_;
v___y_725_ = v_snd_743_;
v___y_727_ = v_snd_741_;
goto _start;
}
}
else
{
lean_dec(v_i_723_);
lean_dec_ref(v_f_720_);
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_f_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_i_750_, lean_object* v_acc_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_747_, v_keys_748_, v_vals_749_, v_i_750_, v_acc_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_f_757_, lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_fst_767_; lean_object* v_snd_768_; lean_object* v_snd_769_; lean_object* v___y_774_; uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
v___x_782_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
switch(lean_obj_tag(v___x_782_))
{
case 0:
{
lean_object* v_key_783_; lean_object* v_val_784_; lean_object* v___x_785_; 
v_key_783_ = lean_ctor_get(v___x_782_, 0);
v_val_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc_ref(v_f_757_);
lean_inc_ref(v___y_763_);
lean_inc(v_val_784_);
lean_inc(v_key_783_);
v___x_785_ = lean_apply_7(v_f_757_, v_b_761_, v_key_783_, v_val_784_, v___y_762_, v___y_763_, v___y_764_, lean_box(0));
v___y_774_ = v___x_785_;
goto v___jp_773_;
}
case 1:
{
lean_object* v_node_786_; lean_object* v___x_787_; 
v_node_786_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_node_786_);
lean_inc_ref(v_f_757_);
v___x_787_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_757_, v_node_786_, v_b_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_774_ = v___x_787_;
goto v___jp_773_;
}
default: 
{
v_fst_767_ = v_b_761_;
v_snd_768_ = v___y_762_;
v_snd_769_ = v___y_764_;
goto v___jp_766_;
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec_ref(v_f_757_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_b_761_);
lean_ctor_set(v___x_788_, 1, v___y_762_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___y_764_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
v___jp_766_:
{
size_t v___x_770_; size_t v___x_771_; 
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_759_, v___x_770_);
v_i_759_ = v___x_771_;
v_b_761_ = v_fst_767_;
v___y_762_ = v_snd_768_;
v___y_764_ = v_snd_769_;
goto _start;
}
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_object* v_a_775_; lean_object* v_fst_776_; 
v_a_775_ = lean_ctor_get(v___y_774_, 0);
v_fst_776_ = lean_ctor_get(v_a_775_, 0);
if (lean_obj_tag(v_fst_776_) == 0)
{
lean_dec_ref(v_f_757_);
return v___y_774_;
}
else
{
lean_object* v_a_777_; lean_object* v_snd_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; 
lean_inc(v_a_775_);
lean_dec_ref_known(v___y_774_, 1);
v_a_777_ = lean_ctor_get(v_fst_776_, 0);
lean_inc(v_a_777_);
v_snd_778_ = lean_ctor_get(v_a_775_, 1);
lean_inc(v_snd_778_);
lean_dec(v_a_775_);
v_fst_779_ = lean_ctor_get(v_a_777_, 0);
lean_inc(v_fst_779_);
v_snd_780_ = lean_ctor_get(v_a_777_, 1);
lean_inc(v_snd_780_);
lean_dec(v_a_777_);
v_fst_767_ = v_fst_779_;
v_snd_768_ = v_snd_780_;
v_snd_769_ = v_snd_778_;
goto v___jp_766_;
}
}
else
{
lean_dec_ref(v_f_757_);
return v___y_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_f_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_es_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_815_; 
v_es_799_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_815_ == 0)
{
v___x_801_ = v_x_793_;
v_isShared_802_ = v_isSharedCheck_815_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_es_799_);
lean_dec(v_x_793_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_815_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v_es_799_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec_ref(v_es_799_);
lean_dec_ref(v_f_792_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_x_794_);
lean_ctor_set(v___x_806_, 1, v___y_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v___x_806_);
v___x_808_ = v___x_801_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___y_797_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
else
{
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_801_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_804_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_792_, v_es_799_, v___x_812_, v___x_813_, v_x_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec_ref(v_es_799_);
return v___x_814_;
}
}
}
else
{
lean_object* v_ks_816_; lean_object* v_vs_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_ks_816_ = lean_ctor_get(v_x_793_, 0);
lean_inc_ref(v_ks_816_);
v_vs_817_ = lean_ctor_get(v_x_793_, 1);
lean_inc_ref(v_vs_817_);
lean_dec_ref_known(v_x_793_, 2);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_792_, v_ks_816_, v_vs_817_, v___x_818_, v_x_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec_ref(v_vs_817_);
lean_dec_ref(v_ks_816_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_f_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_820_, v_x_821_, v_x_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_f_828_, lean_object* v_as_829_, lean_object* v_i_830_, lean_object* v_stop_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_i_boxed_837_; size_t v_stop_boxed_838_; lean_object* v_res_839_; 
v_i_boxed_837_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_stop_boxed_838_ = lean_unbox_usize(v_stop_831_);
lean_dec(v_stop_831_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_828_, v_as_829_, v_i_boxed_837_, v_stop_boxed_838_, v_b_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_as_829_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_840_, lean_object* v_f_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___f_846_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_846_, 0, v_f_841_);
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v___f_846_, v_map_840_, v___x_847_, v___y_842_, v___y_843_, v___y_844_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_849_, lean_object* v_f_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_849_, v_f_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object* v_s_856_, lean_object* v_f_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_map_u2081_862_; lean_object* v_map_u2082_863_; lean_object* v_buckets_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_map_u2081_862_ = lean_ctor_get(v_s_856_, 0);
lean_inc_ref(v_map_u2081_862_);
v_map_u2082_863_ = lean_ctor_get(v_s_856_, 1);
lean_inc_ref(v_map_u2082_863_);
lean_dec_ref(v_s_856_);
v_buckets_864_ = lean_ctor_get(v_map_u2081_862_, 1);
lean_inc_ref(v_buckets_864_);
lean_dec_ref(v_map_u2081_862_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_array_get_size(v_buckets_864_);
v___x_867_ = lean_nat_dec_lt(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec_ref(v_buckets_864_);
v___x_868_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_863_, v_f_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v___x_869_ = lean_box(0);
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_866_);
lean_inc_ref(v_f_857_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_857_, v_buckets_864_, v___x_870_, v___x_871_, v___x_869_, v___y_858_, v___y_859_, v___y_860_);
lean_dec_ref(v_buckets_864_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v_fst_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
v_fst_874_ = lean_ctor_get(v_a_873_, 0);
if (lean_obj_tag(v_fst_874_) == 0)
{
lean_dec(v_a_873_);
lean_dec_ref(v_map_u2082_863_);
lean_dec_ref(v_f_857_);
return v___x_872_;
}
else
{
lean_object* v_a_875_; lean_object* v_snd_876_; lean_object* v_snd_877_; lean_object* v___x_878_; 
lean_dec_ref_known(v___x_872_, 1);
v_a_875_ = lean_ctor_get(v_fst_874_, 0);
lean_inc(v_a_875_);
v_snd_876_ = lean_ctor_get(v_a_873_, 1);
lean_inc(v_snd_876_);
lean_dec(v_a_873_);
v_snd_877_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_snd_877_);
lean_dec(v_a_875_);
v___x_878_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_863_, v_f_857_, v_snd_877_, v___y_859_, v_snd_876_);
return v___x_878_;
}
}
else
{
lean_dec_ref(v_map_u2082_863_);
lean_dec_ref(v_f_857_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object* v_s_879_, lean_object* v_f_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_879_, v_f_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object* v_env_887_, lean_object* v_cliOptions_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___f_892_; lean_object* v_recursorMap_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___f_892_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_893_ = lean_box(1);
v___x_894_ = l_Lean_Environment_constants(v_env_887_);
v___x_895_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v___x_894_, v___f_892_, v_recursorMap_893_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_934_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_934_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_934_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_fst_900_; lean_object* v_snd_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_933_; 
v_fst_900_ = lean_ctor_get(v_a_896_, 0);
v_snd_901_ = lean_ctor_get(v_a_896_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_a_896_);
if (v_isSharedCheck_933_ == 0)
{
v___x_903_ = v_a_896_;
v_isShared_904_ = v_isSharedCheck_933_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_snd_901_);
lean_inc(v_fst_900_);
lean_dec(v_a_896_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_933_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_fst_906_; 
if (lean_obj_tag(v_fst_900_) == 0)
{
lean_object* v_a_930_; 
v_a_930_ = lean_ctor_get(v_fst_900_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v_fst_900_, 1);
v_fst_906_ = v_a_930_;
goto v___jp_905_;
}
else
{
lean_object* v_a_931_; lean_object* v_snd_932_; 
v_a_931_ = lean_ctor_get(v_fst_900_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v_fst_900_, 1);
v_snd_932_ = lean_ctor_get(v_a_931_, 1);
lean_inc(v_snd_932_);
lean_dec(v_a_931_);
v_fst_906_ = v_snd_932_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v_visitedNames_907_; lean_object* v_visitedLevels_908_; lean_object* v_visitedExprs_909_; lean_object* v_visitedConstants_910_; lean_object* v_noMDataExprs_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_928_; 
v_visitedNames_907_ = lean_ctor_get(v_snd_901_, 0);
v_visitedLevels_908_ = lean_ctor_get(v_snd_901_, 1);
v_visitedExprs_909_ = lean_ctor_get(v_snd_901_, 2);
v_visitedConstants_910_ = lean_ctor_get(v_snd_901_, 3);
v_noMDataExprs_911_ = lean_ctor_get(v_snd_901_, 4);
v_isSharedCheck_928_ = !lean_is_exclusive(v_snd_901_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_snd_901_, 5);
lean_dec(v_unused_929_);
v___x_913_ = v_snd_901_;
v_isShared_914_ = v_isSharedCheck_928_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_noMDataExprs_911_);
lean_inc(v_visitedConstants_910_);
lean_inc(v_visitedExprs_909_);
lean_inc(v_visitedLevels_908_);
lean_inc(v_visitedNames_907_);
lean_dec(v_snd_901_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_928_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; uint8_t v___x_918_; lean_object* v___x_920_; 
v___x_915_ = lean_box(0);
v___x_916_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_888_);
v___x_917_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_888_);
v___x_918_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_888_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 5, v_fst_906_);
v___x_920_ = v___x_913_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_visitedNames_907_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_visitedLevels_908_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_visitedExprs_909_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_visitedConstants_910_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_noMDataExprs_911_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_fst_906_);
v___x_920_ = v_reuseFailAlloc_927_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*6, v___x_916_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*6 + 1, v___x_917_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*6 + 2, v___x_918_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_920_);
lean_ctor_set(v___x_903_, 0, v___x_915_);
v___x_922_ = v___x_903_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_922_);
v___x_924_ = v___x_898_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
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
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_a_935_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_895_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_895_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_943_, lean_object* v_cliOptions_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_LeanExport_initState(v_env_943_, v_cliOptions_944_, v_a_945_, v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_cliOptions_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_949_, lean_object* v_k_950_, lean_object* v_t_951_, lean_object* v_hl_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_949_, v_k_950_, v_t_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_954_, lean_object* v_as_955_, lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v_a_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_954_, v_as_x27_956_, v_b_957_, v___y_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_963_, lean_object* v_as_964_, lean_object* v_as_x27_965_, lean_object* v_b_966_, lean_object* v_a_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_963_, v_as_964_, v_as_x27_965_, v_b_966_, v_a_967_, v___y_968_, v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_as_x27_965_);
lean_dec(v_as_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_00_u03b2_972_, lean_object* v_s_973_, lean_object* v_f_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_973_, v_f_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_00_u03b2_980_, lean_object* v_s_981_, lean_object* v_f_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(v_00_u03b2_980_, v_s_981_, v_f_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b2_988_, lean_object* v_f_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_989_, v_x_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b2_997_, lean_object* v_f_998_, lean_object* v_x_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b2_997_, v_f_998_, v_x_999_, v_x_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_1006_, lean_object* v_map_1007_, lean_object* v_f_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_1007_, v_f_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_map_1015_, lean_object* v_f_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1014_, v_map_1015_, v_f_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object* v_00_u03b2_1022_, lean_object* v_f_1023_, lean_object* v_as_1024_, size_t v_i_1025_, size_t v_stop_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_1023_, v_as_1024_, v_i_1025_, v_stop_1026_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_f_1034_, lean_object* v_as_1035_, lean_object* v_i_1036_, lean_object* v_stop_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_i_boxed_1043_; size_t v_stop_boxed_1044_; lean_object* v_res_1045_; 
v_i_boxed_1043_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_stop_boxed_1044_ = lean_unbox_usize(v_stop_1037_);
lean_dec(v_stop_1037_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(v_00_u03b2_1033_, v_f_1034_, v_as_1035_, v_i_boxed_1043_, v_stop_boxed_1044_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_as_1035_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object* v_map_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1047_, v_map_1046_, v_init_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_map_1054_, lean_object* v_f_1055_, lean_object* v_init_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1054_, v_f_1055_, v_init_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object* v_00_u03c3_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_map_1064_, lean_object* v_f_1065_, lean_object* v_init_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1065_, v_map_1064_, v_init_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03c3_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_map_1074_, lean_object* v_f_1075_, lean_object* v_init_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(v_00_u03c3_1072_, v_00_u03b2_1073_, v_map_1074_, v_f_1075_, v_init_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03c3_1082_, lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_f_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1085_, v_x_1086_, v_x_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03c3_1093_, lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_f_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(v_00_u03c3_1093_, v_00_u03b1_1094_, v_00_u03b2_1095_, v_f_1096_, v_x_1097_, v_x_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_00_u03c3_1106_, lean_object* v_f_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_1107_, v_as_1108_, v_i_1109_, v_stop_1110_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_00_u03c3_1119_, lean_object* v_f_1120_, lean_object* v_as_1121_, lean_object* v_i_1122_, lean_object* v_stop_1123_, lean_object* v_b_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_i_boxed_1129_; size_t v_stop_boxed_1130_; lean_object* v_res_1131_; 
v_i_boxed_1129_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_stop_boxed_1130_ = lean_unbox_usize(v_stop_1123_);
lean_dec(v_stop_1123_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_1117_, v_00_u03b2_1118_, v_00_u03c3_1119_, v_f_1120_, v_as_1121_, v_i_boxed_1129_, v_stop_boxed_1130_, v_b_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_as_1121_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object* v_00_u03c3_1132_, lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_f_1135_, lean_object* v_keys_1136_, lean_object* v_vals_1137_, lean_object* v_heq_1138_, lean_object* v_i_1139_, lean_object* v_acc_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_1135_, v_keys_1136_, v_vals_1137_, v_i_1139_, v_acc_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03c3_1146_, lean_object* v_00_u03b1_1147_, lean_object* v_00_u03b2_1148_, lean_object* v_f_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_acc_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(v_00_u03c3_1146_, v_00_u03b1_1147_, v_00_u03b2_1148_, v_f_1149_, v_keys_1150_, v_vals_1151_, v_heq_1152_, v_i_1153_, v_acc_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_vals_1151_);
lean_dec_ref(v_keys_1150_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_, lean_object* v_x_1163_, lean_object* v_namespaced_1164_, lean_object* v_getM_1165_, lean_object* v_setM_1166_, lean_object* v_rec_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_inc_ref(v_getM_1165_);
lean_inc_ref(v_a_1169_);
v___x_1171_ = lean_apply_1(v_getM_1165_, v_a_1169_);
lean_inc(v_x_1163_);
lean_inc_ref(v_inst_1161_);
lean_inc_ref(v_inst_1162_);
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1162_, v_inst_1161_, v___x_1171_, v_x_1163_);
lean_dec_ref(v___x_1171_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_rec_1167_);
lean_dec_ref(v_setM_1166_);
lean_dec_ref(v_getM_1165_);
lean_dec_ref(v_namespaced_1164_);
lean_dec(v_x_1163_);
lean_dec_ref(v_inst_1162_);
lean_dec_ref(v_inst_1161_);
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_val_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_val_1173_);
lean_ctor_set(v___x_1177_, 1, v_a_1169_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v___x_1182_; 
lean_dec(v___x_1172_);
lean_inc_ref(v_a_1168_);
v___x_1182_ = lean_apply_3(v_rec_1167_, v_a_1168_, v_a_1169_, lean_box(0));
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1218_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v_fst_1184_ = lean_ctor_get(v_a_1183_, 0);
v_snd_1185_ = lean_ctor_get(v_a_1183_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_a_1183_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1187_ = v_a_1183_;
v_isShared_1188_ = v_isSharedCheck_1218_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snd_1185_);
lean_inc(v_fst_1184_);
lean_dec(v_a_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1218_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v_size_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_inc(v_snd_1185_);
v___x_1189_ = lean_apply_1(v_getM_1165_, v_snd_1185_);
v_size_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_n(v_size_1190_, 2);
v___f_1191_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
v___x_1192_ = l_Lean_JsonNumber_fromNat(v_size_1190_);
v___x_1193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
v___x_1194_ = l_Lean_Json_setObjVal_x21(v_fst_1184_, v_namespaced_1164_, v___x_1193_);
v___x_1195_ = l_Lean_Json_compress(v___x_1194_);
v___x_1196_ = l_IO_println___redArg(v___f_1191_, v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1208_; 
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1209_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_inc(v_size_1190_);
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1162_, v_inst_1161_, v___x_1189_, v_x_1163_, v_size_1190_);
v___x_1201_ = lean_apply_2(v_setM_1166_, v_snd_1185_, v___x_1200_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v___x_1201_);
lean_ctor_set(v___x_1187_, 0, v_size_1190_);
v___x_1203_ = v___x_1187_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_size_1190_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1203_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_size_1190_);
lean_dec_ref(v___x_1189_);
lean_del_object(v___x_1187_);
lean_dec(v_snd_1185_);
lean_dec_ref(v_setM_1166_);
lean_dec(v_x_1163_);
lean_dec_ref(v_inst_1162_);
lean_dec_ref(v_inst_1161_);
v_a_1210_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1196_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1196_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_setM_1166_);
lean_dec_ref(v_getM_1165_);
lean_dec_ref(v_namespaced_1164_);
lean_dec(v_x_1163_);
lean_dec_ref(v_inst_1162_);
lean_dec_ref(v_inst_1161_);
v_a_1219_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1182_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1182_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_x_1229_, lean_object* v_namespaced_1230_, lean_object* v_getM_1231_, lean_object* v_setM_1232_, lean_object* v_rec_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1227_, v_inst_1228_, v_x_1229_, v_namespaced_1230_, v_getM_1231_, v_setM_1232_, v_rec_1233_, v_a_1234_, v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_x_1241_, lean_object* v_namespaced_1242_, lean_object* v_getM_1243_, lean_object* v_setM_1244_, lean_object* v_rec_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_inc_ref(v_getM_1243_);
lean_inc_ref(v_a_1247_);
v___x_1249_ = lean_apply_1(v_getM_1243_, v_a_1247_);
lean_inc(v_x_1241_);
lean_inc_ref(v_inst_1239_);
lean_inc_ref(v_inst_1240_);
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1240_, v_inst_1239_, v___x_1249_, v_x_1241_);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 1)
{
lean_object* v_val_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_rec_1245_);
lean_dec_ref(v_setM_1244_);
lean_dec_ref(v_getM_1243_);
lean_dec_ref(v_namespaced_1242_);
lean_dec(v_x_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
v_val_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_val_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_val_1251_);
lean_ctor_set(v___x_1255_, 1, v_a_1247_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
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
lean_object* v___x_1260_; 
lean_dec(v___x_1250_);
lean_inc_ref(v_a_1246_);
v___x_1260_ = lean_apply_3(v_rec_1245_, v_a_1246_, v_a_1247_, lean_box(0));
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_fst_1262_; lean_object* v_snd_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1296_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v_fst_1262_ = lean_ctor_get(v_a_1261_, 0);
v_snd_1263_ = lean_ctor_get(v_a_1261_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1261_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1265_ = v_a_1261_;
v_isShared_1266_ = v_isSharedCheck_1296_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1263_);
lean_inc(v_fst_1262_);
lean_dec(v_a_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1296_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v_size_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v_snd_1263_);
v___x_1267_ = lean_apply_1(v_getM_1243_, v_snd_1263_);
v_size_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc_n(v_size_1268_, 2);
v___f_1269_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
v___x_1270_ = l_Lean_JsonNumber_fromNat(v_size_1268_);
v___x_1271_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
v___x_1272_ = l_Lean_Json_setObjVal_x21(v_fst_1262_, v_namespaced_1242_, v___x_1271_);
v___x_1273_ = l_Lean_Json_compress(v___x_1272_);
v___x_1274_ = l_IO_println___redArg(v___f_1269_, v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1274_, 0);
lean_dec(v_unused_1287_);
v___x_1276_ = v___x_1274_;
v_isShared_1277_ = v_isSharedCheck_1286_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___x_1274_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1286_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_inc(v_size_1268_);
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1240_, v_inst_1239_, v___x_1267_, v_x_1241_, v_size_1268_);
v___x_1279_ = lean_apply_2(v_setM_1244_, v_snd_1263_, v___x_1278_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1279_);
lean_ctor_set(v___x_1265_, 0, v_size_1268_);
v___x_1281_ = v___x_1265_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_size_1268_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1281_);
v___x_1283_ = v___x_1276_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_size_1268_);
lean_dec_ref(v___x_1267_);
lean_del_object(v___x_1265_);
lean_dec(v_snd_1263_);
lean_dec_ref(v_setM_1244_);
lean_dec(v_x_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
v_a_1288_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1274_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1274_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_setM_1244_);
lean_dec_ref(v_getM_1243_);
lean_dec_ref(v_namespaced_1242_);
lean_dec(v_x_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec_ref(v_inst_1239_);
v_a_1297_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1260_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1260_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_x_1308_, lean_object* v_namespaced_1309_, lean_object* v_getM_1310_, lean_object* v_setM_1311_, lean_object* v_rec_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1305_, v_inst_1306_, v_inst_1307_, v_x_1308_, v_namespaced_1309_, v_getM_1310_, v_setM_1311_, v_rec_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1316_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_instMonadEIO(lean_box(0));
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v___f_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___f_1335_; lean_object* v___x_1421__overap_1336_; lean_object* v___x_1337_; 
v___x_1322_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1323_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1323_, 0, v___x_1322_);
v___f_1324_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1324_, 0, v___x_1322_);
v___f_1325_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1325_, 0, v___x_1322_);
v___f_1326_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1326_, 0, v___x_1322_);
v___x_1327_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1327_, 0, lean_box(0));
lean_closure_set(v___x_1327_, 1, lean_box(0));
lean_closure_set(v___x_1327_, 2, v___x_1322_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___f_1323_);
v___x_1329_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1329_, 0, lean_box(0));
lean_closure_set(v___x_1329_, 1, lean_box(0));
lean_closure_set(v___x_1329_, 2, v___x_1322_);
v___x_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_ctor_set(v___x_1330_, 2, v___f_1324_);
lean_ctor_set(v___x_1330_, 3, v___f_1325_);
lean_ctor_set(v___x_1330_, 4, v___f_1326_);
v___x_1331_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1331_, 0, lean_box(0));
lean_closure_set(v___x_1331_, 1, lean_box(0));
lean_closure_set(v___x_1331_, 2, v___x_1322_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_box(0);
v___x_1334_ = l_instInhabitedOfMonad___redArg(v___x_1332_, v___x_1333_);
v___f_1335_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1335_, 0, v___x_1334_);
v___x_1421__overap_1336_ = lean_panic_fn_borrowed(v___f_1335_, v_msg_1318_);
lean_dec_ref(v___f_1335_);
lean_inc_ref(v___y_1319_);
v___x_1337_ = lean_apply_3(v___x_1421__overap_1336_, v___y_1319_, v___y_1320_, lean_box(0));
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1343_, lean_object* v_x_1344_){
_start:
{
if (lean_obj_tag(v_x_1344_) == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_box(0);
return v___x_1345_;
}
else
{
lean_object* v_key_1346_; lean_object* v_value_1347_; lean_object* v_tail_1348_; uint8_t v___x_1349_; 
v_key_1346_ = lean_ctor_get(v_x_1344_, 0);
v_value_1347_ = lean_ctor_get(v_x_1344_, 1);
v_tail_1348_ = lean_ctor_get(v_x_1344_, 2);
v___x_1349_ = lean_name_eq(v_key_1346_, v_a_1343_);
if (v___x_1349_ == 0)
{
v_x_1344_ = v_tail_1348_;
goto _start;
}
else
{
lean_object* v___x_1351_; 
lean_inc(v_value_1347_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_value_1347_);
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1352_, v_x_1353_);
lean_dec(v_x_1353_);
lean_dec(v_a_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_buckets_1357_; lean_object* v___x_1358_; uint64_t v___y_1360_; 
v_buckets_1357_ = lean_ctor_get(v_m_1355_, 1);
v___x_1358_ = lean_array_get_size(v_buckets_1357_);
if (lean_obj_tag(v_a_1356_) == 0)
{
uint64_t v___x_1374_; 
v___x_1374_ = 1723ULL;
v___y_1360_ = v___x_1374_;
goto v___jp_1359_;
}
else
{
uint64_t v_hash_1375_; 
v_hash_1375_ = lean_ctor_get_uint64(v_a_1356_, sizeof(void*)*2);
v___y_1360_ = v_hash_1375_;
goto v___jp_1359_;
}
v___jp_1359_:
{
uint64_t v___x_1361_; uint64_t v___x_1362_; uint64_t v_fold_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1361_ = 32ULL;
v___x_1362_ = lean_uint64_shift_right(v___y_1360_, v___x_1361_);
v_fold_1363_ = lean_uint64_xor(v___y_1360_, v___x_1362_);
v___x_1364_ = 16ULL;
v___x_1365_ = lean_uint64_shift_right(v_fold_1363_, v___x_1364_);
v___x_1366_ = lean_uint64_xor(v_fold_1363_, v___x_1365_);
v___x_1367_ = lean_uint64_to_usize(v___x_1366_);
v___x_1368_ = lean_usize_of_nat(v___x_1358_);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_sub(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_usize_land(v___x_1367_, v___x_1370_);
v___x_1372_ = lean_array_uget_borrowed(v_buckets_1357_, v___x_1371_);
v___x_1373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1356_, v___x_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_m_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_putStr_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_get_stdout();
v_putStr_1382_ = lean_ctor_get(v___x_1381_, 4);
lean_inc_ref(v_putStr_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = lean_apply_2(v_putStr_1382_, v_s_1379_, lean_box(0));
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1387_){
_start:
{
uint32_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = 10;
v___x_1390_ = lean_string_push(v_s_1387_, v___x_1389_);
v___x_1391_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1392_);
return v_res_1394_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1399_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1400_ = lean_unsigned_to_nat(18u);
v___x_1401_ = lean_unsigned_to_nat(114u);
v___x_1402_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1403_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1404_ = l_mkPanicMessageWithDecl(v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_, v___x_1399_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_visitedNames_1413_; lean_object* v___x_1414_; 
v_visitedNames_1413_ = lean_ctor_get(v_a_1411_, 0);
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1413_, v_n_1409_);
if (lean_obj_tag(v___x_1414_) == 1)
{
lean_object* v_val_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_n_1409_);
v_val_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_val_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_val_1415_);
lean_ctor_set(v___x_1419_, 1, v_a_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v___x_1424_; lean_object* v_fst_1426_; lean_object* v_snd_1427_; 
lean_dec(v___x_1414_);
v___x_1424_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1409_))
{
case 0:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1469_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1468_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v_fst_1471_; lean_object* v_snd_1472_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v_fst_1471_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_fst_1471_);
v_snd_1472_ = lean_ctor_get(v_a_1470_, 1);
lean_inc(v_snd_1472_);
lean_dec(v_a_1470_);
v_fst_1426_ = v_fst_1471_;
v_snd_1427_ = v_snd_1472_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1469_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1469_);
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
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
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
}
case 1:
{
lean_object* v_pre_1481_; lean_object* v_str_1482_; lean_object* v___x_1483_; 
v_pre_1481_ = lean_ctor_get(v_n_1409_, 0);
v_str_1482_ = lean_ctor_get(v_n_1409_, 1);
lean_inc(v_pre_1481_);
v___x_1483_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1481_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1512_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1512_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1512_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1511_; 
v_fst_1488_ = lean_ctor_get(v_a_1484_, 0);
v_snd_1489_ = lean_ctor_get(v_a_1484_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_a_1484_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1491_ = v_a_1484_;
v_isShared_1492_ = v_isSharedCheck_1511_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_inc(v_fst_1488_);
lean_dec(v_a_1484_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1511_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1493_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1494_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1495_ = l_Lean_JsonNumber_fromNat(v_fst_1488_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 2);
lean_ctor_set(v___x_1486_, 0, v___x_1495_);
v___x_1497_ = v___x_1486_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1497_);
lean_ctor_set(v___x_1491_, 0, v___x_1494_);
v___x_1499_ = v___x_1491_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_inc_ref(v_str_1482_);
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_str_1482_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1493_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1499_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_Json_mkObj(v___x_1504_);
lean_dec_ref_known(v___x_1504_, 2);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1493_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v___x_1502_);
v___x_1508_ = l_Lean_Json_mkObj(v___x_1507_);
lean_dec_ref_known(v___x_1507_, 2);
v_fst_1426_ = v___x_1508_;
v_snd_1427_ = v_snd_1489_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1409_, 2);
return v___x_1483_;
}
}
default: 
{
lean_object* v_pre_1513_; lean_object* v_i_1514_; lean_object* v___x_1515_; 
v_pre_1513_ = lean_ctor_get(v_n_1409_, 0);
v_i_1514_ = lean_ctor_get(v_n_1409_, 1);
lean_inc(v_pre_1513_);
v___x_1515_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1513_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1546_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1546_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; lean_object* v_snd_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1545_; 
v_fst_1520_ = lean_ctor_get(v_a_1516_, 0);
v_snd_1521_ = lean_ctor_get(v_a_1516_, 1);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_a_1516_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1523_ = v_a_1516_;
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_snd_1521_);
lean_inc(v_fst_1520_);
lean_dec(v_a_1516_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1545_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1525_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1526_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1527_ = l_Lean_JsonNumber_fromNat(v_fst_1520_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 2);
lean_ctor_set(v___x_1518_, 0, v___x_1527_);
v___x_1529_ = v___x_1518_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1529_);
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1531_ = v___x_1523_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1532_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1514_);
v___x_1533_ = l_Lean_JsonNumber_fromNat(v_i_1514_);
v___x_1534_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1532_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1531_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_Json_mkObj(v___x_1538_);
lean_dec_ref_known(v___x_1538_, 2);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1525_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1536_);
v___x_1542_ = l_Lean_Json_mkObj(v___x_1541_);
lean_dec_ref_known(v___x_1541_, 2);
v_fst_1426_ = v___x_1542_;
v_snd_1427_ = v_snd_1521_;
goto v___jp_1425_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1409_, 2);
return v___x_1515_;
}
}
}
v___jp_1425_:
{
lean_object* v_visitedNames_1428_; lean_object* v_visitedLevels_1429_; lean_object* v_visitedExprs_1430_; lean_object* v_visitedConstants_1431_; lean_object* v_noMDataExprs_1432_; uint8_t v_exportMData_1433_; uint8_t v_exportUnsafe_1434_; uint8_t v_ignoreMissing_1435_; lean_object* v_recursorMap_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1467_; 
v_visitedNames_1428_ = lean_ctor_get(v_snd_1427_, 0);
v_visitedLevels_1429_ = lean_ctor_get(v_snd_1427_, 1);
v_visitedExprs_1430_ = lean_ctor_get(v_snd_1427_, 2);
v_visitedConstants_1431_ = lean_ctor_get(v_snd_1427_, 3);
v_noMDataExprs_1432_ = lean_ctor_get(v_snd_1427_, 4);
v_exportMData_1433_ = lean_ctor_get_uint8(v_snd_1427_, sizeof(void*)*6);
v_exportUnsafe_1434_ = lean_ctor_get_uint8(v_snd_1427_, sizeof(void*)*6 + 1);
v_ignoreMissing_1435_ = lean_ctor_get_uint8(v_snd_1427_, sizeof(void*)*6 + 2);
v_recursorMap_1436_ = lean_ctor_get(v_snd_1427_, 5);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_snd_1427_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1438_ = v_snd_1427_;
v_isShared_1439_ = v_isSharedCheck_1467_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_recursorMap_1436_);
lean_inc(v_noMDataExprs_1432_);
lean_inc(v_visitedConstants_1431_);
lean_inc(v_visitedExprs_1430_);
lean_inc(v_visitedLevels_1429_);
lean_inc(v_visitedNames_1428_);
lean_dec(v_snd_1427_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1467_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_size_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_size_1440_ = lean_ctor_get(v_visitedNames_1428_, 0);
lean_inc_n(v_size_1440_, 2);
v___x_1441_ = l_Lean_JsonNumber_fromNat(v_size_1440_);
v___x_1442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = l_Lean_Json_setObjVal_x21(v_fst_1426_, v___x_1424_, v___x_1442_);
v___x_1444_ = l_Lean_Json_compress(v___x_1443_);
v___x_1445_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1458_);
v___x_1447_ = v___x_1445_;
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1445_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_inc(v_size_1440_);
v___x_1449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1428_, v_n_1409_, v_size_1440_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1449_);
v___x_1451_ = v___x_1438_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_visitedLevels_1429_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_visitedExprs_1430_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_visitedConstants_1431_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_noMDataExprs_1432_);
lean_ctor_set(v_reuseFailAlloc_1456_, 5, v_recursorMap_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*6, v_exportMData_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*6 + 1, v_exportUnsafe_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*6 + 2, v_ignoreMissing_1435_);
v___x_1451_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_size_1440_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1452_);
v___x_1454_ = v___x_1447_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_size_1440_);
lean_del_object(v___x_1438_);
lean_dec(v_recursorMap_1436_);
lean_dec_ref(v_noMDataExprs_1432_);
lean_dec_ref(v_visitedConstants_1431_);
lean_dec_ref(v_visitedExprs_1430_);
lean_dec_ref(v_visitedLevels_1429_);
lean_dec_ref(v_visitedNames_1428_);
lean_dec(v_n_1409_);
v_a_1459_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1445_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1445_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1552_, lean_object* v_m_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1553_, v_a_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1556_, v_m_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_m_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1560_, lean_object* v_a_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1561_, v_x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1564_, lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1564_, v_a_1565_, v_x_1566_);
lean_dec(v_x_1566_);
lean_dec(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
else
{
lean_object* v_key_1571_; lean_object* v_value_1572_; lean_object* v_tail_1573_; uint8_t v___x_1574_; 
v_key_1571_ = lean_ctor_get(v_x_1569_, 0);
v_value_1572_ = lean_ctor_get(v_x_1569_, 1);
v_tail_1573_ = lean_ctor_get(v_x_1569_, 2);
v___x_1574_ = lean_level_eq(v_key_1571_, v_a_1568_);
if (v___x_1574_ == 0)
{
v_x_1569_ = v_tail_1573_;
goto _start;
}
else
{
lean_object* v___x_1576_; 
lean_inc(v_value_1572_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_value_1572_);
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1577_, v_x_1578_);
lean_dec(v_x_1578_);
lean_dec(v_a_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_buckets_1582_; lean_object* v___x_1583_; uint64_t v___x_1584_; uint64_t v___x_1585_; uint64_t v___x_1586_; uint64_t v_fold_1587_; uint64_t v___x_1588_; uint64_t v___x_1589_; uint64_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; size_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_buckets_1582_ = lean_ctor_get(v_m_1580_, 1);
v___x_1583_ = lean_array_get_size(v_buckets_1582_);
v___x_1584_ = l_Lean_Level_hash(v_a_1581_);
v___x_1585_ = 32ULL;
v___x_1586_ = lean_uint64_shift_right(v___x_1584_, v___x_1585_);
v_fold_1587_ = lean_uint64_xor(v___x_1584_, v___x_1586_);
v___x_1588_ = 16ULL;
v___x_1589_ = lean_uint64_shift_right(v_fold_1587_, v___x_1588_);
v___x_1590_ = lean_uint64_xor(v_fold_1587_, v___x_1589_);
v___x_1591_ = lean_uint64_to_usize(v___x_1590_);
v___x_1592_ = lean_usize_of_nat(v___x_1583_);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_sub(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_usize_land(v___x_1591_, v___x_1594_);
v___x_1596_ = lean_array_uget_borrowed(v_buckets_1582_, v___x_1595_);
v___x_1597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1581_, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_m_1598_);
return v_res_1600_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1607_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1608_ = lean_unsigned_to_nat(23u);
v___x_1609_ = lean_unsigned_to_nat(132u);
v___x_1610_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1611_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1612_ = l_mkPanicMessageWithDecl(v___x_1611_, v___x_1610_, v___x_1609_, v___x_1608_, v___x_1607_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_visitedLevels_1617_; lean_object* v___x_1618_; 
v_visitedLevels_1617_ = lean_ctor_get(v_a_1615_, 1);
v___x_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1617_, v_l_1613_);
if (lean_obj_tag(v___x_1618_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v_l_1613_);
v_val_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_val_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_val_1619_);
lean_ctor_set(v___x_1623_, 1, v_a_1615_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1625_ = v___x_1621_;
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
}
else
{
lean_object* v___x_1628_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; 
lean_dec(v___x_1618_);
v___x_1628_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1613_))
{
case 1:
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_ctor_get(v_l_1613_, 0);
lean_inc(v_a_1672_);
v___x_1673_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1672_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1695_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1695_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1695_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1694_; 
v_fst_1678_ = lean_ctor_get(v_a_1674_, 0);
v_snd_1679_ = lean_ctor_get(v_a_1674_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_a_1674_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1681_ = v_a_1674_;
v_isShared_1682_ = v_isSharedCheck_1694_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snd_1679_);
lean_inc(v_fst_1678_);
lean_dec(v_a_1674_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1694_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1684_ = l_Lean_JsonNumber_fromNat(v_fst_1678_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 2);
lean_ctor_set(v___x_1676_, 0, v___x_1684_);
v___x_1686_ = v___x_1676_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1686_);
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1688_ = v___x_1681_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l_Lean_Json_mkObj(v___x_1690_);
lean_dec_ref_known(v___x_1690_, 2);
v_fst_1630_ = v___x_1691_;
v_snd_1631_ = v_snd_1679_;
goto v___jp_1629_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1613_, 1);
return v___x_1673_;
}
}
case 2:
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v___x_1698_; 
v_a_1696_ = lean_ctor_get(v_l_1613_, 0);
v_a_1697_ = lean_ctor_get(v_l_1613_, 1);
lean_inc(v_a_1696_);
v___x_1698_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1696_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1743_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1743_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1743_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_fst_1703_; lean_object* v_snd_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1742_; 
v_fst_1703_ = lean_ctor_get(v_a_1699_, 0);
v_snd_1704_ = lean_ctor_get(v_a_1699_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1699_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1706_ = v_a_1699_;
v_isShared_1707_ = v_isSharedCheck_1742_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_snd_1704_);
lean_inc(v_fst_1703_);
lean_dec(v_a_1699_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1742_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; 
lean_inc(v_a_1697_);
v___x_1708_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1697_, v_a_1614_, v_snd_1704_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1741_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1741_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1741_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_fst_1713_; lean_object* v_snd_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1740_; 
v_fst_1713_ = lean_ctor_get(v_a_1709_, 0);
v_snd_1714_ = lean_ctor_get(v_a_1709_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_a_1709_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1716_ = v_a_1709_;
v_isShared_1717_ = v_isSharedCheck_1740_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_snd_1714_);
lean_inc(v_fst_1713_);
lean_dec(v_a_1709_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1740_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1718_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1719_ = l_Lean_JsonNumber_fromNat(v_fst_1703_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 2);
lean_ctor_set(v___x_1711_, 0, v___x_1719_);
v___x_1721_ = v___x_1711_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_JsonNumber_fromNat(v_fst_1713_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 2);
lean_ctor_set(v___x_1701_, 0, v___x_1722_);
v___x_1724_ = v___x_1701_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1725_ = lean_unsigned_to_nat(2u);
v___x_1726_ = lean_mk_empty_array_with_capacity(v___x_1725_);
v___x_1727_ = lean_array_push(v___x_1726_, v___x_1721_);
v___x_1728_ = lean_array_push(v___x_1727_, v___x_1724_);
v___x_1729_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1729_);
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1731_ = v___x_1716_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
lean_ctor_set(v___x_1706_, 1, v___x_1732_);
lean_ctor_set(v___x_1706_, 0, v___x_1731_);
v___x_1734_ = v___x_1706_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Json_mkObj(v___x_1734_);
lean_dec_ref(v___x_1734_);
v_fst_1630_ = v___x_1735_;
v_snd_1631_ = v_snd_1714_;
goto v___jp_1629_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1706_);
lean_dec(v_fst_1703_);
lean_del_object(v___x_1701_);
lean_dec_ref_known(v_l_1613_, 2);
return v___x_1708_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1613_, 2);
return v___x_1698_;
}
}
case 3:
{
lean_object* v_a_1744_; lean_object* v_a_1745_; lean_object* v___x_1746_; 
v_a_1744_ = lean_ctor_get(v_l_1613_, 0);
v_a_1745_ = lean_ctor_get(v_l_1613_, 1);
lean_inc(v_a_1744_);
v___x_1746_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1744_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1791_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1791_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1791_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1790_; 
v_fst_1751_ = lean_ctor_get(v_a_1747_, 0);
v_snd_1752_ = lean_ctor_get(v_a_1747_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_a_1747_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1754_ = v_a_1747_;
v_isShared_1755_ = v_isSharedCheck_1790_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snd_1752_);
lean_inc(v_fst_1751_);
lean_dec(v_a_1747_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1790_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; 
lean_inc(v_a_1745_);
v___x_1756_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1745_, v_a_1614_, v_snd_1752_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1789_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1789_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1789_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1788_; 
v_fst_1761_ = lean_ctor_get(v_a_1757_, 0);
v_snd_1762_ = lean_ctor_get(v_a_1757_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_a_1757_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1764_ = v_a_1757_;
v_isShared_1765_ = v_isSharedCheck_1788_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snd_1762_);
lean_inc(v_fst_1761_);
lean_dec(v_a_1757_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1788_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_1767_ = l_Lean_JsonNumber_fromNat(v_fst_1751_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 2);
lean_ctor_set(v___x_1759_, 0, v___x_1767_);
v___x_1769_ = v___x_1759_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = l_Lean_JsonNumber_fromNat(v_fst_1761_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 2);
lean_ctor_set(v___x_1749_, 0, v___x_1770_);
v___x_1772_ = v___x_1749_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1773_ = lean_unsigned_to_nat(2u);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___x_1775_ = lean_array_push(v___x_1774_, v___x_1769_);
v___x_1776_ = lean_array_push(v___x_1775_, v___x_1772_);
v___x_1777_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1777_);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1779_ = v___x_1764_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 1);
lean_ctor_set(v___x_1754_, 1, v___x_1780_);
lean_ctor_set(v___x_1754_, 0, v___x_1779_);
v___x_1782_ = v___x_1754_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Json_mkObj(v___x_1782_);
lean_dec_ref(v___x_1782_);
v_fst_1630_ = v___x_1783_;
v_snd_1631_ = v_snd_1762_;
goto v___jp_1629_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1754_);
lean_dec(v_fst_1751_);
lean_del_object(v___x_1749_);
lean_dec_ref_known(v_l_1613_, 2);
return v___x_1756_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1613_, 2);
return v___x_1746_;
}
}
case 4:
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v_l_1613_, 0);
lean_inc(v_a_1792_);
v___x_1793_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_1792_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1815_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1815_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1815_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1814_; 
v_fst_1798_ = lean_ctor_get(v_a_1794_, 0);
v_snd_1799_ = lean_ctor_get(v_a_1794_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1794_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1801_ = v_a_1794_;
v_isShared_1802_ = v_isSharedCheck_1814_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
lean_dec(v_a_1794_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1814_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_1804_ = l_Lean_JsonNumber_fromNat(v_fst_1798_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 2);
lean_ctor_set(v___x_1796_, 0, v___x_1804_);
v___x_1806_ = v___x_1796_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1806_);
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1808_ = v___x_1801_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_box(0);
v___x_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_Json_mkObj(v___x_1810_);
lean_dec_ref_known(v___x_1810_, 2);
v_fst_1630_ = v___x_1811_;
v_snd_1631_ = v_snd_1799_;
goto v___jp_1629_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1613_, 1);
return v___x_1793_;
}
}
default: 
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_1817_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1816_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v_fst_1819_ = lean_ctor_get(v_a_1818_, 0);
lean_inc(v_fst_1819_);
v_snd_1820_ = lean_ctor_get(v_a_1818_, 1);
lean_inc(v_snd_1820_);
lean_dec(v_a_1818_);
v_fst_1630_ = v_fst_1819_;
v_snd_1631_ = v_snd_1820_;
goto v___jp_1629_;
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_l_1613_);
v_a_1821_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1817_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1817_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
v___jp_1629_:
{
lean_object* v_visitedLevels_1632_; lean_object* v_visitedNames_1633_; lean_object* v_visitedExprs_1634_; lean_object* v_visitedConstants_1635_; lean_object* v_noMDataExprs_1636_; uint8_t v_exportMData_1637_; uint8_t v_exportUnsafe_1638_; uint8_t v_ignoreMissing_1639_; lean_object* v_recursorMap_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1671_; 
v_visitedLevels_1632_ = lean_ctor_get(v_snd_1631_, 1);
v_visitedNames_1633_ = lean_ctor_get(v_snd_1631_, 0);
v_visitedExprs_1634_ = lean_ctor_get(v_snd_1631_, 2);
v_visitedConstants_1635_ = lean_ctor_get(v_snd_1631_, 3);
v_noMDataExprs_1636_ = lean_ctor_get(v_snd_1631_, 4);
v_exportMData_1637_ = lean_ctor_get_uint8(v_snd_1631_, sizeof(void*)*6);
v_exportUnsafe_1638_ = lean_ctor_get_uint8(v_snd_1631_, sizeof(void*)*6 + 1);
v_ignoreMissing_1639_ = lean_ctor_get_uint8(v_snd_1631_, sizeof(void*)*6 + 2);
v_recursorMap_1640_ = lean_ctor_get(v_snd_1631_, 5);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_snd_1631_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1642_ = v_snd_1631_;
v_isShared_1643_ = v_isSharedCheck_1671_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_recursorMap_1640_);
lean_inc(v_noMDataExprs_1636_);
lean_inc(v_visitedConstants_1635_);
lean_inc(v_visitedExprs_1634_);
lean_inc(v_visitedLevels_1632_);
lean_inc(v_visitedNames_1633_);
lean_dec(v_snd_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1671_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_size_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_size_1644_ = lean_ctor_get(v_visitedLevels_1632_, 0);
lean_inc_n(v_size_1644_, 2);
v___x_1645_ = l_Lean_JsonNumber_fromNat(v_size_1644_);
v___x_1646_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
v___x_1647_ = l_Lean_Json_setObjVal_x21(v_fst_1630_, v___x_1628_, v___x_1646_);
v___x_1648_ = l_Lean_Json_compress(v___x_1647_);
v___x_1649_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1661_; 
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1649_, 0);
lean_dec(v_unused_1662_);
v___x_1651_ = v___x_1649_;
v_isShared_1652_ = v_isSharedCheck_1661_;
goto v_resetjp_1650_;
}
else
{
lean_dec(v___x_1649_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1661_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_inc(v_size_1644_);
v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1632_, v_l_1613_, v_size_1644_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1653_);
v___x_1655_ = v___x_1642_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_visitedNames_1633_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_visitedExprs_1634_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_visitedConstants_1635_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_noMDataExprs_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v_recursorMap_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*6, v_exportMData_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*6 + 1, v_exportUnsafe_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*6 + 2, v_ignoreMissing_1639_);
v___x_1655_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_size_1644_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1656_);
v___x_1658_ = v___x_1651_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_size_1644_);
lean_del_object(v___x_1642_);
lean_dec(v_recursorMap_1640_);
lean_dec_ref(v_noMDataExprs_1636_);
lean_dec_ref(v_visitedConstants_1635_);
lean_dec_ref(v_visitedExprs_1634_);
lean_dec_ref(v_visitedNames_1633_);
lean_dec_ref(v_visitedLevels_1632_);
lean_dec(v_l_1613_);
v_a_1663_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1649_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1649_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1829_, v_a_1830_, v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_1834_, lean_object* v_m_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1835_, v_a_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_m_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_1838_, v_m_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_m_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_1842_, lean_object* v_a_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1843_, v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1846_, lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_1846_, v_a_1847_, v_x_1848_);
lean_dec(v_x_1848_);
lean_dec(v_a_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
if (lean_obj_tag(v_a_1850_) == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = l_List_reverse___redArg(v_a_1851_);
return v___x_1852_;
}
else
{
lean_object* v_head_1853_; lean_object* v_tail_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
v_head_1853_ = lean_ctor_get(v_a_1850_, 0);
v_tail_1854_ = lean_ctor_get(v_a_1850_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1850_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1856_ = v_a_1850_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_tail_1854_);
lean_inc(v_head_1853_);
lean_dec(v_a_1850_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = l_Lean_Level_param___override(v_head_1853_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v_a_1851_);
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_a_1851_);
v___x_1860_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
v_a_1850_ = v_tail_1854_;
v_a_1851_ = v___x_1860_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_1864_, size_t v_i_1865_, lean_object* v_bs_1866_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_usize_dec_lt(v_i_1865_, v_sz_1864_);
if (v___x_1867_ == 0)
{
return v_bs_1866_;
}
else
{
lean_object* v_v_1868_; lean_object* v___x_1869_; lean_object* v_bs_x27_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v_v_1868_ = lean_array_uget(v_bs_1866_, v_i_1865_);
v___x_1869_ = lean_unsigned_to_nat(0u);
v_bs_x27_1870_ = lean_array_uset(v_bs_1866_, v_i_1865_, v___x_1869_);
v___x_1871_ = l_Lean_JsonNumber_fromNat(v_v_1868_);
v___x_1872_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
v___x_1873_ = ((size_t)1ULL);
v___x_1874_ = lean_usize_add(v_i_1865_, v___x_1873_);
v___x_1875_ = lean_array_uset(v_bs_x27_1870_, v_i_1865_, v___x_1872_);
v_i_1865_ = v___x_1874_;
v_bs_1866_ = v___x_1875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1877_, lean_object* v_i_1878_, lean_object* v_bs_1879_){
_start:
{
size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1877_);
lean_dec(v_sz_1877_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_1883_){
_start:
{
size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_sz_1884_ = lean_array_size(v_a_1883_);
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1884_, v___x_1885_, v_a_1883_);
v___x_1887_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_array_mk(v_a_1888_);
v___x_1890_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
if (lean_obj_tag(v_x_1891_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = l_List_reverse___redArg(v_x_1892_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___y_1894_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v_head_1899_; lean_object* v_tail_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1920_; 
v_head_1899_ = lean_ctor_get(v_x_1891_, 0);
v_tail_1900_ = lean_ctor_get(v_x_1891_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1891_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1902_ = v_x_1891_;
v_isShared_1903_ = v_isSharedCheck_1920_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_tail_1900_);
lean_inc(v_head_1899_);
lean_dec(v_x_1891_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1920_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_1899_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1909_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v_fst_1906_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_fst_1906_);
v_snd_1907_ = lean_ctor_get(v_a_1905_, 1);
lean_inc(v_snd_1907_);
lean_dec(v_a_1905_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_x_1892_);
lean_ctor_set(v___x_1902_, 0, v_fst_1906_);
v___x_1909_ = v___x_1902_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_fst_1906_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_x_1892_);
v___x_1909_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v_x_1891_ = v_tail_1900_;
v_x_1892_ = v___x_1909_;
v___y_1894_ = v_snd_1907_;
goto _start;
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_del_object(v___x_1902_);
lean_dec(v_tail_1900_);
lean_dec(v_x_1892_);
v_a_1912_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1904_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1921_, v_x_1922_, v___y_1923_, v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = l_List_reverse___redArg(v_x_1928_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___y_1930_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1956_; 
v_head_1935_ = lean_ctor_get(v_x_1927_, 0);
v_tail_1936_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1938_ = v_x_1927_;
v_isShared_1939_ = v_isSharedCheck_1956_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_tail_1936_);
lean_inc(v_head_1935_);
lean_dec(v_x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1956_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_1935_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v_fst_1942_ = lean_ctor_get(v_a_1941_, 0);
lean_inc(v_fst_1942_);
v_snd_1943_ = lean_ctor_get(v_a_1941_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_a_1941_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v_x_1928_);
lean_ctor_set(v___x_1938_, 0, v_fst_1942_);
v___x_1945_ = v___x_1938_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_x_1928_);
v___x_1945_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
v_x_1927_ = v_tail_1936_;
v_x_1928_ = v___x_1945_;
v___y_1930_ = v_snd_1943_;
goto _start;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1938_);
lean_dec(v_tail_1936_);
lean_dec(v_x_1928_);
v_a_1948_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1940_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1940_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1957_, v_x_1958_, v___y_1959_, v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_box(0);
lean_inc(v_uparams_1963_);
v___x_1968_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_1963_, v___x_1967_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_fst_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_fst_1970_);
v_snd_1971_ = lean_ctor_get(v_a_1969_, 1);
lean_inc(v_snd_1971_);
lean_dec(v_a_1969_);
v___x_1972_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_1963_, v___x_1967_);
v___x_1973_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_1972_, v___x_1967_, v_a_1964_, v_snd_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1991_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1991_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1991_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_snd_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1989_; 
v_snd_1978_ = lean_ctor_get(v_a_1974_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1974_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v_a_1974_, 0);
lean_dec(v_unused_1990_);
v___x_1980_ = v_a_1974_;
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_snd_1978_);
lean_dec(v_a_1974_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_1970_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_snd_1978_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1984_);
v___x_1986_ = v___x_1976_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_fst_1970_);
v_a_1992_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1973_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1973_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
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
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_uparams_1963_);
v_a_2000_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1968_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1968_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2013_, v___x_2017_, v_a_2014_, v_a_2015_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2036_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2036_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2035_; 
v_fst_2023_ = lean_ctor_get(v_a_2019_, 0);
v_snd_2024_ = lean_ctor_get(v_a_2019_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2026_ = v_a_2019_;
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snd_2024_);
lean_inc(v_fst_2023_);
lean_dec(v_a_2019_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2023_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2028_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_snd_2024_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2030_);
v___x_2032_ = v___x_2021_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
v_a_2037_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2018_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2018_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2045_, v_a_2046_, v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v___f_2055_; lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___f_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___f_2067_; lean_object* v___x_11487__overap_2068_; lean_object* v___x_2069_; 
v___x_2054_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2055_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2055_, 0, v___x_2054_);
v___f_2056_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2056_, 0, v___x_2054_);
v___f_2057_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2057_, 0, v___x_2054_);
v___f_2058_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2058_, 0, v___x_2054_);
v___x_2059_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2059_, 0, lean_box(0));
lean_closure_set(v___x_2059_, 1, lean_box(0));
lean_closure_set(v___x_2059_, 2, v___x_2054_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___f_2055_);
v___x_2061_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2061_, 0, lean_box(0));
lean_closure_set(v___x_2061_, 1, lean_box(0));
lean_closure_set(v___x_2061_, 2, v___x_2054_);
v___x_2062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_ctor_set(v___x_2062_, 2, v___f_2056_);
lean_ctor_set(v___x_2062_, 3, v___f_2057_);
lean_ctor_set(v___x_2062_, 4, v___f_2058_);
v___x_2063_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2063_, 0, lean_box(0));
lean_closure_set(v___x_2063_, 1, lean_box(0));
lean_closure_set(v___x_2063_, 2, v___x_2054_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lean_instInhabitedExpr;
v___x_2066_ = l_instInhabitedOfMonad___redArg(v___x_2064_, v___x_2065_);
v___f_2067_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2067_, 0, v___x_2066_);
v___x_11487__overap_2068_ = lean_panic_fn_borrowed(v___f_2067_, v_msg_2050_);
lean_dec_ref(v___f_2067_);
lean_inc_ref(v___y_2051_);
v___x_2069_ = lean_apply_3(v___x_11487__overap_2068_, v___y_2051_, v___y_2052_, lean_box(0));
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2070_, v___y_2071_, v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2075_, lean_object* v_b_2076_, lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_dec(v_b_2076_);
lean_dec_ref(v_a_2075_);
return v_x_2077_;
}
else
{
lean_object* v_key_2078_; lean_object* v_value_2079_; lean_object* v_tail_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2092_; 
v_key_2078_ = lean_ctor_get(v_x_2077_, 0);
v_value_2079_ = lean_ctor_get(v_x_2077_, 1);
v_tail_2080_ = lean_ctor_get(v_x_2077_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2082_ = v_x_2077_;
v_isShared_2083_ = v_isSharedCheck_2092_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_tail_2080_);
lean_inc(v_value_2079_);
lean_inc(v_key_2078_);
lean_dec(v_x_2077_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2092_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_expr_eqv(v_key_2078_, v_a_2075_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2075_, v_b_2076_, v_tail_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 2, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_key_2078_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_value_2079_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
else
{
lean_object* v___x_2090_; 
lean_dec(v_value_2079_);
lean_dec(v_key_2078_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_b_2076_);
lean_ctor_set(v___x_2082_, 0, v_a_2075_);
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2075_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_b_2076_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_tail_2080_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2094_) == 0)
{
return v_x_2093_;
}
else
{
lean_object* v_key_2095_; lean_object* v_value_2096_; lean_object* v_tail_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2120_; 
v_key_2095_ = lean_ctor_get(v_x_2094_, 0);
v_value_2096_ = lean_ctor_get(v_x_2094_, 1);
v_tail_2097_ = lean_ctor_get(v_x_2094_, 2);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2094_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2099_ = v_x_2094_;
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_tail_2097_);
lean_inc(v_value_2096_);
lean_inc(v_key_2095_);
lean_dec(v_x_2094_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2120_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; uint64_t v___x_2102_; uint64_t v___x_2103_; uint64_t v___x_2104_; uint64_t v_fold_2105_; uint64_t v___x_2106_; uint64_t v___x_2107_; uint64_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2101_ = lean_array_get_size(v_x_2093_);
v___x_2102_ = l_Lean_Expr_hash(v_key_2095_);
v___x_2103_ = 32ULL;
v___x_2104_ = lean_uint64_shift_right(v___x_2102_, v___x_2103_);
v_fold_2105_ = lean_uint64_xor(v___x_2102_, v___x_2104_);
v___x_2106_ = 16ULL;
v___x_2107_ = lean_uint64_shift_right(v_fold_2105_, v___x_2106_);
v___x_2108_ = lean_uint64_xor(v_fold_2105_, v___x_2107_);
v___x_2109_ = lean_uint64_to_usize(v___x_2108_);
v___x_2110_ = lean_usize_of_nat(v___x_2101_);
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_sub(v___x_2110_, v___x_2111_);
v___x_2113_ = lean_usize_land(v___x_2109_, v___x_2112_);
v___x_2114_ = lean_array_uget_borrowed(v_x_2093_, v___x_2113_);
lean_inc(v___x_2114_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 2, v___x_2114_);
v___x_2116_ = v___x_2099_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_key_2095_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_value_2096_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_array_uset(v_x_2093_, v___x_2113_, v___x_2116_);
v_x_2093_ = v___x_2117_;
v_x_2094_ = v_tail_2097_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2121_, lean_object* v_source_2122_, lean_object* v_target_2123_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_source_2122_);
v___x_2125_ = lean_nat_dec_lt(v_i_2121_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v_source_2122_);
lean_dec(v_i_2121_);
return v_target_2123_;
}
else
{
lean_object* v_es_2126_; lean_object* v___x_2127_; lean_object* v_source_2128_; lean_object* v_target_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_es_2126_ = lean_array_fget(v_source_2122_, v_i_2121_);
v___x_2127_ = lean_box(0);
v_source_2128_ = lean_array_fset(v_source_2122_, v_i_2121_, v___x_2127_);
v_target_2129_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2123_, v_es_2126_);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_add(v_i_2121_, v___x_2130_);
lean_dec(v_i_2121_);
v_i_2121_ = v___x_2131_;
v_source_2122_ = v_source_2128_;
v_target_2123_ = v_target_2129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2133_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_nbuckets_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2134_ = lean_array_get_size(v_data_2133_);
v___x_2135_ = lean_unsigned_to_nat(2u);
v_nbuckets_2136_ = lean_nat_mul(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_mk_array(v_nbuckets_2136_, v___x_2138_);
v___x_2140_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2137_, v_data_2133_, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
if (lean_obj_tag(v_x_2142_) == 0)
{
uint8_t v___x_2143_; 
v___x_2143_ = 0;
return v___x_2143_;
}
else
{
lean_object* v_key_2144_; lean_object* v_tail_2145_; uint8_t v___x_2146_; 
v_key_2144_ = lean_ctor_get(v_x_2142_, 0);
v_tail_2145_ = lean_ctor_get(v_x_2142_, 2);
v___x_2146_ = lean_expr_eqv(v_key_2144_, v_a_2141_);
if (v___x_2146_ == 0)
{
v_x_2142_ = v_tail_2145_;
goto _start;
}
else
{
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2148_, lean_object* v_x_2149_){
_start:
{
uint8_t v_res_2150_; lean_object* v_r_2151_; 
v_res_2150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2148_, v_x_2149_);
lean_dec(v_x_2149_);
lean_dec_ref(v_a_2148_);
v_r_2151_ = lean_box(v_res_2150_);
return v_r_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2152_, lean_object* v_a_2153_, lean_object* v_b_2154_){
_start:
{
lean_object* v_size_2155_; lean_object* v_buckets_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2199_; 
v_size_2155_ = lean_ctor_get(v_m_2152_, 0);
v_buckets_2156_ = lean_ctor_get(v_m_2152_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_m_2152_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2158_ = v_m_2152_;
v_isShared_2159_ = v_isSharedCheck_2199_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_buckets_2156_);
lean_inc(v_size_2155_);
lean_dec(v_m_2152_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2199_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; uint64_t v___x_2163_; uint64_t v_fold_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; uint64_t v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; lean_object* v_bkt_2173_; uint8_t v___x_2174_; 
v___x_2160_ = lean_array_get_size(v_buckets_2156_);
v___x_2161_ = l_Lean_Expr_hash(v_a_2153_);
v___x_2162_ = 32ULL;
v___x_2163_ = lean_uint64_shift_right(v___x_2161_, v___x_2162_);
v_fold_2164_ = lean_uint64_xor(v___x_2161_, v___x_2163_);
v___x_2165_ = 16ULL;
v___x_2166_ = lean_uint64_shift_right(v_fold_2164_, v___x_2165_);
v___x_2167_ = lean_uint64_xor(v_fold_2164_, v___x_2166_);
v___x_2168_ = lean_uint64_to_usize(v___x_2167_);
v___x_2169_ = lean_usize_of_nat(v___x_2160_);
v___x_2170_ = ((size_t)1ULL);
v___x_2171_ = lean_usize_sub(v___x_2169_, v___x_2170_);
v___x_2172_ = lean_usize_land(v___x_2168_, v___x_2171_);
v_bkt_2173_ = lean_array_uget_borrowed(v_buckets_2156_, v___x_2172_);
v___x_2174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2153_, v_bkt_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v_size_x27_2176_; lean_object* v___x_2177_; lean_object* v_buckets_x27_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2175_ = lean_unsigned_to_nat(1u);
v_size_x27_2176_ = lean_nat_add(v_size_2155_, v___x_2175_);
lean_dec(v_size_2155_);
lean_inc(v_bkt_2173_);
v___x_2177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2177_, 0, v_a_2153_);
lean_ctor_set(v___x_2177_, 1, v_b_2154_);
lean_ctor_set(v___x_2177_, 2, v_bkt_2173_);
v_buckets_x27_2178_ = lean_array_uset(v_buckets_2156_, v___x_2172_, v___x_2177_);
v___x_2179_ = lean_unsigned_to_nat(4u);
v___x_2180_ = lean_nat_mul(v_size_x27_2176_, v___x_2179_);
v___x_2181_ = lean_unsigned_to_nat(3u);
v___x_2182_ = lean_nat_div(v___x_2180_, v___x_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_array_get_size(v_buckets_x27_2178_);
v___x_2184_ = lean_nat_dec_le(v___x_2182_, v___x_2183_);
lean_dec(v___x_2182_);
if (v___x_2184_ == 0)
{
lean_object* v_val_2185_; lean_object* v___x_2187_; 
v_val_2185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2178_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v_val_2185_);
lean_ctor_set(v___x_2158_, 0, v_size_x27_2176_);
v___x_2187_ = v___x_2158_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_size_x27_2176_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_val_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
else
{
lean_object* v___x_2190_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v_buckets_x27_2178_);
lean_ctor_set(v___x_2158_, 0, v_size_x27_2176_);
v___x_2190_ = v___x_2158_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_x27_2176_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_buckets_x27_2178_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v_buckets_x27_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_inc(v_bkt_2173_);
v___x_2192_ = lean_box(0);
v_buckets_x27_2193_ = lean_array_uset(v_buckets_2156_, v___x_2172_, v___x_2192_);
v___x_2194_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2153_, v_b_2154_, v_bkt_2173_);
v___x_2195_ = lean_array_uset(v_buckets_x27_2193_, v___x_2172_, v___x_2194_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v___x_2195_);
v___x_2197_ = v___x_2158_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_size_2155_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2200_, lean_object* v_x_2201_){
_start:
{
if (lean_obj_tag(v_x_2201_) == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_box(0);
return v___x_2202_;
}
else
{
lean_object* v_key_2203_; lean_object* v_value_2204_; lean_object* v_tail_2205_; uint8_t v___x_2206_; 
v_key_2203_ = lean_ctor_get(v_x_2201_, 0);
v_value_2204_ = lean_ctor_get(v_x_2201_, 1);
v_tail_2205_ = lean_ctor_get(v_x_2201_, 2);
v___x_2206_ = lean_expr_eqv(v_key_2203_, v_a_2200_);
if (v___x_2206_ == 0)
{
v_x_2201_ = v_tail_2205_;
goto _start;
}
else
{
lean_object* v___x_2208_; 
lean_inc(v_value_2204_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_value_2204_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2209_, v_x_2210_);
lean_dec(v_x_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_buckets_2214_; lean_object* v___x_2215_; uint64_t v___x_2216_; uint64_t v___x_2217_; uint64_t v___x_2218_; uint64_t v_fold_2219_; uint64_t v___x_2220_; uint64_t v___x_2221_; uint64_t v___x_2222_; size_t v___x_2223_; size_t v___x_2224_; size_t v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_buckets_2214_ = lean_ctor_get(v_m_2212_, 1);
v___x_2215_ = lean_array_get_size(v_buckets_2214_);
v___x_2216_ = l_Lean_Expr_hash(v_a_2213_);
v___x_2217_ = 32ULL;
v___x_2218_ = lean_uint64_shift_right(v___x_2216_, v___x_2217_);
v_fold_2219_ = lean_uint64_xor(v___x_2216_, v___x_2218_);
v___x_2220_ = 16ULL;
v___x_2221_ = lean_uint64_shift_right(v_fold_2219_, v___x_2220_);
v___x_2222_ = lean_uint64_xor(v_fold_2219_, v___x_2221_);
v___x_2223_ = lean_uint64_to_usize(v___x_2222_);
v___x_2224_ = lean_usize_of_nat(v___x_2215_);
v___x_2225_ = ((size_t)1ULL);
v___x_2226_ = lean_usize_sub(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_usize_land(v___x_2223_, v___x_2226_);
v___x_2228_ = lean_array_uget_borrowed(v_buckets_2214_, v___x_2227_);
v___x_2229_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2213_, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2230_, v_a_2231_);
lean_dec_ref(v_a_2231_);
lean_dec_ref(v_m_2230_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2234_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2235_ = lean_unsigned_to_nat(26u);
v___x_2236_ = lean_unsigned_to_nat(152u);
v___x_2237_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2238_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2239_ = l_mkPanicMessageWithDecl(v___x_2238_, v___x_2237_, v___x_2236_, v___x_2235_, v___x_2234_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_e_x27_2245_; lean_object* v_visitedNames_2246_; lean_object* v_visitedLevels_2247_; lean_object* v_visitedExprs_2248_; lean_object* v_visitedConstants_2249_; lean_object* v_noMDataExprs_2250_; uint8_t v_exportMData_2251_; uint8_t v_exportUnsafe_2252_; uint8_t v_ignoreMissing_2253_; lean_object* v_recursorMap_2254_; lean_object* v_e_x27_2260_; lean_object* v___y_2261_; lean_object* v_visitedNames_2271_; lean_object* v_visitedLevels_2272_; lean_object* v_visitedExprs_2273_; lean_object* v_visitedConstants_2274_; lean_object* v_noMDataExprs_2275_; uint8_t v_exportMData_2276_; uint8_t v_exportUnsafe_2277_; uint8_t v_ignoreMissing_2278_; lean_object* v_recursorMap_2279_; lean_object* v___x_2280_; 
v_visitedNames_2271_ = lean_ctor_get(v_a_2242_, 0);
v_visitedLevels_2272_ = lean_ctor_get(v_a_2242_, 1);
v_visitedExprs_2273_ = lean_ctor_get(v_a_2242_, 2);
v_visitedConstants_2274_ = lean_ctor_get(v_a_2242_, 3);
v_noMDataExprs_2275_ = lean_ctor_get(v_a_2242_, 4);
v_exportMData_2276_ = lean_ctor_get_uint8(v_a_2242_, sizeof(void*)*6);
v_exportUnsafe_2277_ = lean_ctor_get_uint8(v_a_2242_, sizeof(void*)*6 + 1);
v_ignoreMissing_2278_ = lean_ctor_get_uint8(v_a_2242_, sizeof(void*)*6 + 2);
v_recursorMap_2279_ = lean_ctor_get(v_a_2242_, 5);
v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2275_, v_e_2240_);
if (lean_obj_tag(v___x_2280_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref(v_e_2240_);
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_val_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_val_2281_);
lean_ctor_set(v___x_2285_, 1, v_a_2242_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_dec(v___x_2280_);
switch(lean_obj_tag(v_e_2240_))
{
case 1:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2291_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2290_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v_fst_2293_; lean_object* v_snd_2294_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v_fst_2293_ = lean_ctor_get(v_a_2292_, 0);
lean_inc(v_fst_2293_);
v_snd_2294_ = lean_ctor_get(v_a_2292_, 1);
lean_inc(v_snd_2294_);
lean_dec(v_a_2292_);
v_e_x27_2260_ = v_fst_2293_;
v___y_2261_ = v_snd_2294_;
goto v___jp_2259_;
}
else
{
lean_dec_ref_known(v_e_2240_, 1);
return v___x_2291_;
}
}
case 2:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2296_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2295_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v_fst_2298_; lean_object* v_snd_2299_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v_fst_2298_ = lean_ctor_get(v_a_2297_, 0);
lean_inc(v_fst_2298_);
v_snd_2299_ = lean_ctor_get(v_a_2297_, 1);
lean_inc(v_snd_2299_);
lean_dec(v_a_2297_);
v_e_x27_2260_ = v_fst_2298_;
v___y_2261_ = v_snd_2299_;
goto v___jp_2259_;
}
else
{
lean_dec_ref_known(v_e_2240_, 1);
return v___x_2296_;
}
}
case 5:
{
lean_object* v_fn_2300_; lean_object* v_arg_2301_; lean_object* v___x_2302_; 
v_fn_2300_ = lean_ctor_get(v_e_2240_, 0);
v_arg_2301_ = lean_ctor_get(v_e_2240_, 1);
lean_inc_ref(v_fn_2300_);
v___x_2302_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2300_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2306_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v_fst_2304_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_fst_2304_);
v_snd_2305_ = lean_ctor_get(v_a_2303_, 1);
lean_inc(v_snd_2305_);
lean_dec(v_a_2303_);
lean_inc_ref(v_arg_2301_);
v___x_2306_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2301_, v_a_2241_, v_snd_2305_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v_fst_2308_; lean_object* v_snd_2309_; size_t v___x_2310_; size_t v___x_2311_; uint8_t v___x_2312_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v_fst_2308_ = lean_ctor_get(v_a_2307_, 0);
lean_inc(v_fst_2308_);
v_snd_2309_ = lean_ctor_get(v_a_2307_, 1);
lean_inc(v_snd_2309_);
lean_dec(v_a_2307_);
v___x_2310_ = lean_ptr_addr(v_fn_2300_);
v___x_2311_ = lean_ptr_addr(v_fst_2304_);
v___x_2312_ = lean_usize_dec_eq(v___x_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Expr_app___override(v_fst_2304_, v_fst_2308_);
v_e_x27_2260_ = v___x_2313_;
v___y_2261_ = v_snd_2309_;
goto v___jp_2259_;
}
else
{
size_t v___x_2314_; size_t v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = lean_ptr_addr(v_arg_2301_);
v___x_2315_ = lean_ptr_addr(v_fst_2308_);
v___x_2316_ = lean_usize_dec_eq(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Expr_app___override(v_fst_2304_, v_fst_2308_);
v_e_x27_2260_ = v___x_2317_;
v___y_2261_ = v_snd_2309_;
goto v___jp_2259_;
}
else
{
lean_dec(v_fst_2308_);
lean_dec(v_fst_2304_);
lean_inc_ref(v_e_2240_);
v_e_x27_2260_ = v_e_2240_;
v___y_2261_ = v_snd_2309_;
goto v___jp_2259_;
}
}
}
else
{
lean_dec(v_fst_2304_);
lean_dec_ref_known(v_e_2240_, 2);
return v___x_2306_;
}
}
else
{
lean_dec_ref_known(v_e_2240_, 2);
return v___x_2302_;
}
}
case 6:
{
lean_object* v_binderName_2318_; lean_object* v_binderType_2319_; lean_object* v_body_2320_; uint8_t v_binderInfo_2321_; lean_object* v___x_2322_; 
v_binderName_2318_ = lean_ctor_get(v_e_2240_, 0);
v_binderType_2319_ = lean_ctor_get(v_e_2240_, 1);
v_body_2320_ = lean_ctor_get(v_e_2240_, 2);
v_binderInfo_2321_ = lean_ctor_get_uint8(v_e_2240_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2319_);
v___x_2322_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2319_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_fst_2324_; lean_object* v_snd_2325_; lean_object* v___x_2326_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v_fst_2324_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_fst_2324_);
v_snd_2325_ = lean_ctor_get(v_a_2323_, 1);
lean_inc(v_snd_2325_);
lean_dec(v_a_2323_);
lean_inc_ref(v_body_2320_);
v___x_2326_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2320_, v_a_2241_, v_snd_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_fst_2328_; lean_object* v_snd_2329_; size_t v___x_2330_; size_t v___x_2331_; uint8_t v___x_2332_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_fst_2328_ = lean_ctor_get(v_a_2327_, 0);
lean_inc(v_fst_2328_);
v_snd_2329_ = lean_ctor_get(v_a_2327_, 1);
lean_inc(v_snd_2329_);
lean_dec(v_a_2327_);
v___x_2330_ = lean_ptr_addr(v_binderType_2319_);
v___x_2331_ = lean_ptr_addr(v_fst_2324_);
v___x_2332_ = lean_usize_dec_eq(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_inc(v_binderName_2318_);
v___x_2333_ = l_Lean_Expr_lam___override(v_binderName_2318_, v_fst_2324_, v_fst_2328_, v_binderInfo_2321_);
v_e_x27_2260_ = v___x_2333_;
v___y_2261_ = v_snd_2329_;
goto v___jp_2259_;
}
else
{
size_t v___x_2334_; size_t v___x_2335_; uint8_t v___x_2336_; 
v___x_2334_ = lean_ptr_addr(v_body_2320_);
v___x_2335_ = lean_ptr_addr(v_fst_2328_);
v___x_2336_ = lean_usize_dec_eq(v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_inc(v_binderName_2318_);
v___x_2337_ = l_Lean_Expr_lam___override(v_binderName_2318_, v_fst_2324_, v_fst_2328_, v_binderInfo_2321_);
v_e_x27_2260_ = v___x_2337_;
v___y_2261_ = v_snd_2329_;
goto v___jp_2259_;
}
else
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2321_, v_binderInfo_2321_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
lean_inc(v_binderName_2318_);
v___x_2339_ = l_Lean_Expr_lam___override(v_binderName_2318_, v_fst_2324_, v_fst_2328_, v_binderInfo_2321_);
v_e_x27_2260_ = v___x_2339_;
v___y_2261_ = v_snd_2329_;
goto v___jp_2259_;
}
else
{
lean_dec(v_fst_2328_);
lean_dec(v_fst_2324_);
lean_inc_ref(v_e_2240_);
v_e_x27_2260_ = v_e_2240_;
v___y_2261_ = v_snd_2329_;
goto v___jp_2259_;
}
}
}
}
else
{
lean_dec(v_fst_2324_);
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2326_;
}
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2322_;
}
}
case 7:
{
lean_object* v_binderName_2340_; lean_object* v_binderType_2341_; lean_object* v_body_2342_; uint8_t v_binderInfo_2343_; lean_object* v___x_2344_; 
v_binderName_2340_ = lean_ctor_get(v_e_2240_, 0);
v_binderType_2341_ = lean_ctor_get(v_e_2240_, 1);
v_body_2342_ = lean_ctor_get(v_e_2240_, 2);
v_binderInfo_2343_ = lean_ctor_get_uint8(v_e_2240_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2341_);
v___x_2344_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2341_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v_fst_2346_; lean_object* v_snd_2347_; lean_object* v___x_2348_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v_fst_2346_ = lean_ctor_get(v_a_2345_, 0);
lean_inc(v_fst_2346_);
v_snd_2347_ = lean_ctor_get(v_a_2345_, 1);
lean_inc(v_snd_2347_);
lean_dec(v_a_2345_);
lean_inc_ref(v_body_2342_);
v___x_2348_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2342_, v_a_2241_, v_snd_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_fst_2350_; lean_object* v_snd_2351_; size_t v___x_2352_; size_t v___x_2353_; uint8_t v___x_2354_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_fst_2350_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_fst_2350_);
v_snd_2351_ = lean_ctor_get(v_a_2349_, 1);
lean_inc(v_snd_2351_);
lean_dec(v_a_2349_);
v___x_2352_ = lean_ptr_addr(v_binderType_2341_);
v___x_2353_ = lean_ptr_addr(v_fst_2346_);
v___x_2354_ = lean_usize_dec_eq(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_inc(v_binderName_2340_);
v___x_2355_ = l_Lean_Expr_forallE___override(v_binderName_2340_, v_fst_2346_, v_fst_2350_, v_binderInfo_2343_);
v_e_x27_2260_ = v___x_2355_;
v___y_2261_ = v_snd_2351_;
goto v___jp_2259_;
}
else
{
size_t v___x_2356_; size_t v___x_2357_; uint8_t v___x_2358_; 
v___x_2356_ = lean_ptr_addr(v_body_2342_);
v___x_2357_ = lean_ptr_addr(v_fst_2350_);
v___x_2358_ = lean_usize_dec_eq(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; 
lean_inc(v_binderName_2340_);
v___x_2359_ = l_Lean_Expr_forallE___override(v_binderName_2340_, v_fst_2346_, v_fst_2350_, v_binderInfo_2343_);
v_e_x27_2260_ = v___x_2359_;
v___y_2261_ = v_snd_2351_;
goto v___jp_2259_;
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2343_, v_binderInfo_2343_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_inc(v_binderName_2340_);
v___x_2361_ = l_Lean_Expr_forallE___override(v_binderName_2340_, v_fst_2346_, v_fst_2350_, v_binderInfo_2343_);
v_e_x27_2260_ = v___x_2361_;
v___y_2261_ = v_snd_2351_;
goto v___jp_2259_;
}
else
{
lean_dec(v_fst_2350_);
lean_dec(v_fst_2346_);
lean_inc_ref(v_e_2240_);
v_e_x27_2260_ = v_e_2240_;
v___y_2261_ = v_snd_2351_;
goto v___jp_2259_;
}
}
}
}
else
{
lean_dec(v_fst_2346_);
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2348_;
}
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2344_;
}
}
case 8:
{
lean_object* v_declName_2362_; lean_object* v_type_2363_; lean_object* v_value_2364_; lean_object* v_body_2365_; uint8_t v_nondep_2366_; lean_object* v___x_2367_; 
v_declName_2362_ = lean_ctor_get(v_e_2240_, 0);
v_type_2363_ = lean_ctor_get(v_e_2240_, 1);
v_value_2364_ = lean_ctor_get(v_e_2240_, 2);
v_body_2365_ = lean_ctor_get(v_e_2240_, 3);
v_nondep_2366_ = lean_ctor_get_uint8(v_e_2240_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2363_);
v___x_2367_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2363_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v_fst_2369_; lean_object* v_snd_2370_; lean_object* v___x_2371_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v_fst_2369_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_fst_2369_);
v_snd_2370_ = lean_ctor_get(v_a_2368_, 1);
lean_inc(v_snd_2370_);
lean_dec(v_a_2368_);
lean_inc_ref(v_value_2364_);
v___x_2371_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2364_, v_a_2241_, v_snd_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v_fst_2373_; lean_object* v_snd_2374_; lean_object* v___x_2375_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v_fst_2373_ = lean_ctor_get(v_a_2372_, 0);
lean_inc(v_fst_2373_);
v_snd_2374_ = lean_ctor_get(v_a_2372_, 1);
lean_inc(v_snd_2374_);
lean_dec(v_a_2372_);
lean_inc_ref(v_body_2365_);
v___x_2375_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2365_, v_a_2241_, v_snd_2374_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v_fst_2377_; lean_object* v_snd_2378_; uint8_t v___x_2379_; size_t v___x_2380_; size_t v___x_2381_; uint8_t v___x_2382_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v_fst_2377_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_fst_2377_);
v_snd_2378_ = lean_ctor_get(v_a_2376_, 1);
lean_inc(v_snd_2378_);
lean_dec(v_a_2376_);
v___x_2379_ = 0;
v___x_2380_ = lean_ptr_addr(v_type_2363_);
v___x_2381_ = lean_ptr_addr(v_fst_2369_);
v___x_2382_ = lean_usize_dec_eq(v___x_2380_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
lean_inc(v_declName_2362_);
v___x_2383_ = l_Lean_Expr_letE___override(v_declName_2362_, v_fst_2369_, v_fst_2373_, v_fst_2377_, v___x_2379_);
v_e_x27_2260_ = v___x_2383_;
v___y_2261_ = v_snd_2378_;
goto v___jp_2259_;
}
else
{
size_t v___x_2384_; size_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2384_ = lean_ptr_addr(v_value_2364_);
v___x_2385_ = lean_ptr_addr(v_fst_2373_);
v___x_2386_ = lean_usize_dec_eq(v___x_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_inc(v_declName_2362_);
v___x_2387_ = l_Lean_Expr_letE___override(v_declName_2362_, v_fst_2369_, v_fst_2373_, v_fst_2377_, v___x_2379_);
v_e_x27_2260_ = v___x_2387_;
v___y_2261_ = v_snd_2378_;
goto v___jp_2259_;
}
else
{
size_t v___x_2388_; size_t v___x_2389_; uint8_t v___x_2390_; 
v___x_2388_ = lean_ptr_addr(v_body_2365_);
v___x_2389_ = lean_ptr_addr(v_fst_2377_);
v___x_2390_ = lean_usize_dec_eq(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_inc(v_declName_2362_);
v___x_2391_ = l_Lean_Expr_letE___override(v_declName_2362_, v_fst_2369_, v_fst_2373_, v_fst_2377_, v___x_2379_);
v_e_x27_2260_ = v___x_2391_;
v___y_2261_ = v_snd_2378_;
goto v___jp_2259_;
}
else
{
if (v_nondep_2366_ == 0)
{
lean_dec(v_fst_2377_);
lean_dec(v_fst_2373_);
lean_dec(v_fst_2369_);
lean_inc_ref(v_e_2240_);
v_e_x27_2260_ = v_e_2240_;
v___y_2261_ = v_snd_2378_;
goto v___jp_2259_;
}
else
{
lean_object* v___x_2392_; 
lean_inc(v_declName_2362_);
v___x_2392_ = l_Lean_Expr_letE___override(v_declName_2362_, v_fst_2369_, v_fst_2373_, v_fst_2377_, v___x_2379_);
v_e_x27_2260_ = v___x_2392_;
v___y_2261_ = v_snd_2378_;
goto v___jp_2259_;
}
}
}
}
}
else
{
lean_dec(v_fst_2373_);
lean_dec(v_fst_2369_);
lean_dec_ref_known(v_e_2240_, 4);
return v___x_2375_;
}
}
else
{
lean_dec(v_fst_2369_);
lean_dec_ref_known(v_e_2240_, 4);
return v___x_2371_;
}
}
else
{
lean_dec_ref_known(v_e_2240_, 4);
return v___x_2367_;
}
}
case 10:
{
lean_object* v_expr_2393_; lean_object* v___x_2394_; 
v_expr_2393_ = lean_ctor_get(v_e_2240_, 1);
lean_inc_ref(v_expr_2393_);
v___x_2394_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2393_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_fst_2396_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2396_);
v_snd_2397_ = lean_ctor_get(v_a_2395_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_a_2395_);
v_e_x27_2260_ = v_fst_2396_;
v___y_2261_ = v_snd_2397_;
goto v___jp_2259_;
}
else
{
lean_dec_ref_known(v_e_2240_, 2);
return v___x_2394_;
}
}
case 11:
{
lean_object* v_typeName_2398_; lean_object* v_idx_2399_; lean_object* v_struct_2400_; lean_object* v___x_2401_; 
v_typeName_2398_ = lean_ctor_get(v_e_2240_, 0);
v_idx_2399_ = lean_ctor_get(v_e_2240_, 1);
v_struct_2400_ = lean_ctor_get(v_e_2240_, 2);
lean_inc_ref(v_struct_2400_);
v___x_2401_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2400_, v_a_2241_, v_a_2242_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v_fst_2403_; lean_object* v_snd_2404_; size_t v___x_2405_; size_t v___x_2406_; uint8_t v___x_2407_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v_fst_2403_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_fst_2403_);
v_snd_2404_ = lean_ctor_get(v_a_2402_, 1);
lean_inc(v_snd_2404_);
lean_dec(v_a_2402_);
v___x_2405_ = lean_ptr_addr(v_struct_2400_);
v___x_2406_ = lean_ptr_addr(v_fst_2403_);
v___x_2407_ = lean_usize_dec_eq(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
lean_inc(v_idx_2399_);
lean_inc(v_typeName_2398_);
v___x_2408_ = l_Lean_Expr_proj___override(v_typeName_2398_, v_idx_2399_, v_fst_2403_);
v_e_x27_2260_ = v___x_2408_;
v___y_2261_ = v_snd_2404_;
goto v___jp_2259_;
}
else
{
lean_dec(v_fst_2403_);
lean_inc_ref(v_e_2240_);
v_e_x27_2260_ = v_e_2240_;
v___y_2261_ = v_snd_2404_;
goto v___jp_2259_;
}
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2401_;
}
}
default: 
{
lean_inc(v_recursorMap_2279_);
lean_inc_ref(v_noMDataExprs_2275_);
lean_inc_ref(v_visitedConstants_2274_);
lean_inc_ref(v_visitedExprs_2273_);
lean_inc_ref(v_visitedLevels_2272_);
lean_inc_ref(v_visitedNames_2271_);
lean_dec_ref(v_a_2242_);
lean_inc_ref(v_e_2240_);
v_e_x27_2245_ = v_e_2240_;
v_visitedNames_2246_ = v_visitedNames_2271_;
v_visitedLevels_2247_ = v_visitedLevels_2272_;
v_visitedExprs_2248_ = v_visitedExprs_2273_;
v_visitedConstants_2249_ = v_visitedConstants_2274_;
v_noMDataExprs_2250_ = v_noMDataExprs_2275_;
v_exportMData_2251_ = v_exportMData_2276_;
v_exportUnsafe_2252_ = v_exportUnsafe_2277_;
v_ignoreMissing_2253_ = v_ignoreMissing_2278_;
v_recursorMap_2254_ = v_recursorMap_2279_;
goto v___jp_2244_;
}
}
}
v___jp_2244_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_inc_ref(v_e_x27_2245_);
v___x_2255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2250_, v_e_2240_, v_e_x27_2245_);
v___x_2256_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2256_, 0, v_visitedNames_2246_);
lean_ctor_set(v___x_2256_, 1, v_visitedLevels_2247_);
lean_ctor_set(v___x_2256_, 2, v_visitedExprs_2248_);
lean_ctor_set(v___x_2256_, 3, v_visitedConstants_2249_);
lean_ctor_set(v___x_2256_, 4, v___x_2255_);
lean_ctor_set(v___x_2256_, 5, v_recursorMap_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*6, v_exportMData_2251_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*6 + 1, v_exportUnsafe_2252_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*6 + 2, v_ignoreMissing_2253_);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_e_x27_2245_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
v___jp_2259_:
{
lean_object* v_visitedNames_2262_; lean_object* v_visitedLevels_2263_; lean_object* v_visitedExprs_2264_; lean_object* v_visitedConstants_2265_; lean_object* v_noMDataExprs_2266_; uint8_t v_exportMData_2267_; uint8_t v_exportUnsafe_2268_; uint8_t v_ignoreMissing_2269_; lean_object* v_recursorMap_2270_; 
v_visitedNames_2262_ = lean_ctor_get(v___y_2261_, 0);
lean_inc_ref(v_visitedNames_2262_);
v_visitedLevels_2263_ = lean_ctor_get(v___y_2261_, 1);
lean_inc_ref(v_visitedLevels_2263_);
v_visitedExprs_2264_ = lean_ctor_get(v___y_2261_, 2);
lean_inc_ref(v_visitedExprs_2264_);
v_visitedConstants_2265_ = lean_ctor_get(v___y_2261_, 3);
lean_inc_ref(v_visitedConstants_2265_);
v_noMDataExprs_2266_ = lean_ctor_get(v___y_2261_, 4);
lean_inc_ref(v_noMDataExprs_2266_);
v_exportMData_2267_ = lean_ctor_get_uint8(v___y_2261_, sizeof(void*)*6);
v_exportUnsafe_2268_ = lean_ctor_get_uint8(v___y_2261_, sizeof(void*)*6 + 1);
v_ignoreMissing_2269_ = lean_ctor_get_uint8(v___y_2261_, sizeof(void*)*6 + 2);
v_recursorMap_2270_ = lean_ctor_get(v___y_2261_, 5);
lean_inc(v_recursorMap_2270_);
lean_dec_ref(v___y_2261_);
v_e_x27_2245_ = v_e_x27_2260_;
v_visitedNames_2246_ = v_visitedNames_2262_;
v_visitedLevels_2247_ = v_visitedLevels_2263_;
v_visitedExprs_2248_ = v_visitedExprs_2264_;
v_visitedConstants_2249_ = v_visitedConstants_2265_;
v_noMDataExprs_2250_ = v_noMDataExprs_2266_;
v_exportMData_2251_ = v_exportMData_2267_;
v_exportUnsafe_2252_ = v_exportUnsafe_2268_;
v_ignoreMissing_2253_ = v_ignoreMissing_2269_;
v_recursorMap_2254_ = v_recursorMap_2270_;
goto v___jp_2244_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2409_, v_a_2410_, v_a_2411_);
lean_dec_ref(v_a_2410_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2414_, lean_object* v_m_2415_, lean_object* v_a_2416_, lean_object* v_b_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2415_, v_a_2416_, v_b_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2419_, lean_object* v_m_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2420_, v_a_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2423_, lean_object* v_m_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2423_, v_m_2424_, v_a_2425_);
lean_dec_ref(v_a_2425_);
lean_dec_ref(v_m_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2427_, lean_object* v_a_2428_, lean_object* v_x_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2428_, v_x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2431_, lean_object* v_a_2432_, lean_object* v_x_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2431_, v_a_2432_, v_x_2433_);
lean_dec(v_x_2433_);
lean_dec_ref(v_a_2432_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2436_, lean_object* v_data_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2439_, lean_object* v_a_2440_, lean_object* v_b_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2440_, v_b_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2444_, lean_object* v_a_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2445_, v_x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_a_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2448_, v_a_2449_, v_x_2450_);
lean_dec(v_x_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2452_, lean_object* v_i_2453_, lean_object* v_source_2454_, lean_object* v_target_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2453_, v_source_2454_, v_target_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2464_ = l_Lean_Json_mkObj(v_fields_2461_);
v___x_2465_ = l_Lean_Json_compress(v___x_2464_);
v___x_2466_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2465_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2475_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2475_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2467_);
lean_ctor_set(v___x_2471_, 1, v_a_2462_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_a_2462_);
v_a_2476_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2466_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2466_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2484_, v_a_2485_);
lean_dec(v_fields_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2488_, v_a_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2493_, v_a_2494_, v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_fields_2493_);
return v_res_2497_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Array_instInhabited(lean_box(0));
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___x_162743__overap_2518_; lean_object* v___x_2519_; 
v___x_2503_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2504_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2504_, 0, v___x_2503_);
v___f_2505_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2505_, 0, v___x_2503_);
v___f_2506_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2506_, 0, v___x_2503_);
v___f_2507_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2507_, 0, v___x_2503_);
v___x_2508_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2508_, 0, lean_box(0));
lean_closure_set(v___x_2508_, 1, lean_box(0));
lean_closure_set(v___x_2508_, 2, v___x_2503_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___f_2504_);
v___x_2510_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2510_, 0, lean_box(0));
lean_closure_set(v___x_2510_, 1, lean_box(0));
lean_closure_set(v___x_2510_, 2, v___x_2503_);
v___x_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
lean_ctor_set(v___x_2511_, 2, v___f_2505_);
lean_ctor_set(v___x_2511_, 3, v___f_2506_);
lean_ctor_set(v___x_2511_, 4, v___f_2507_);
v___x_2512_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2512_, 0, lean_box(0));
lean_closure_set(v___x_2512_, 1, lean_box(0));
lean_closure_set(v___x_2512_, 2, v___x_2503_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__4___closed__0);
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
v___x_2516_ = l_instInhabitedOfMonad___redArg(v___x_2513_, v___x_2515_);
v___f_2517_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2517_, 0, v___x_2516_);
v___x_162743__overap_2518_ = lean_panic_fn_borrowed(v___f_2517_, v_msg_2499_);
lean_dec_ref(v___f_2517_);
lean_inc_ref(v___y_2500_);
v___x_2519_ = lean_apply_3(v___x_162743__overap_2518_, v___y_2500_, v___y_2501_, lean_box(0));
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2520_, v___y_2521_, v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___f_2531_; lean_object* v___f_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_162755__overap_2543_; lean_object* v___x_2544_; 
v___x_2529_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2530_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
v___f_2531_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2531_, 0, v___x_2529_);
v___f_2532_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2532_, 0, v___x_2529_);
v___f_2533_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2533_, 0, v___x_2529_);
v___x_2534_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2534_, 0, lean_box(0));
lean_closure_set(v___x_2534_, 1, lean_box(0));
lean_closure_set(v___x_2534_, 2, v___x_2529_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___f_2530_);
v___x_2536_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2536_, 0, lean_box(0));
lean_closure_set(v___x_2536_, 1, lean_box(0));
lean_closure_set(v___x_2536_, 2, v___x_2529_);
v___x_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_ctor_set(v___x_2537_, 2, v___f_2531_);
lean_ctor_set(v___x_2537_, 3, v___f_2532_);
lean_ctor_set(v___x_2537_, 4, v___f_2533_);
v___x_2538_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2538_, 0, lean_box(0));
lean_closure_set(v___x_2538_, 1, lean_box(0));
lean_closure_set(v___x_2538_, 2, v___x_2529_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_box(0);
v___x_2541_ = l_instInhabitedOfMonad___redArg(v___x_2539_, v___x_2540_);
v___f_2542_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2542_, 0, v___x_2541_);
v___x_162755__overap_2543_ = lean_panic_fn_borrowed(v___f_2542_, v_msg_2525_);
lean_dec_ref(v___f_2542_);
lean_inc_ref(v___y_2526_);
v___x_2544_ = lean_apply_3(v___x_162755__overap_2543_, v___y_2526_, v___y_2527_, lean_box(0));
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2545_, v___y_2546_, v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2552_ = lean_panic_fn_borrowed(v___x_2551_, v_msg_2550_);
return v___x_2552_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2555_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__1));
v___x_2556_ = lean_unsigned_to_nat(8u);
v___x_2557_ = lean_unsigned_to_nat(354u);
v___x_2558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2559_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2560_ = l_mkPanicMessageWithDecl(v___x_2559_, v___x_2558_, v___x_2557_, v___x_2556_, v___x_2555_);
return v___x_2560_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__3));
v___x_2563_ = lean_unsigned_to_nat(13u);
v___x_2564_ = lean_unsigned_to_nat(356u);
v___x_2565_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2566_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2571_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__7));
v___x_2572_ = lean_unsigned_to_nat(14u);
v___x_2573_ = lean_unsigned_to_nat(22u);
v___x_2574_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__6));
v___x_2575_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__5));
v___x_2576_ = l_mkPanicMessageWithDecl(v___x_2575_, v___x_2574_, v___x_2573_, v___x_2572_, v___x_2571_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(uint8_t v___x_2577_, lean_object* v_init_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_d_2584_; lean_object* v___y_2585_; 
if (lean_obj_tag(v_x_2579_) == 0)
{
lean_object* v_k_2589_; lean_object* v_l_2590_; lean_object* v_r_2591_; lean_object* v___x_2592_; 
v_k_2589_ = lean_ctor_get(v_x_2579_, 1);
lean_inc(v_k_2589_);
v_l_2590_ = lean_ctor_get(v_x_2579_, 3);
lean_inc(v_l_2590_);
v_r_2591_ = lean_ctor_get(v_x_2579_, 4);
lean_inc(v_r_2591_);
lean_dec_ref_known(v_x_2579_, 5);
v___x_2592_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_2577_, v_init_2578_, v_l_2590_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v_fst_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v_fst_2594_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_fst_2594_);
if (lean_obj_tag(v_fst_2594_) == 0)
{
lean_object* v_snd_2595_; lean_object* v_a_2596_; 
lean_dec(v_r_2591_);
lean_dec(v_k_2589_);
v_snd_2595_ = lean_ctor_get(v_a_2593_, 1);
lean_inc(v_snd_2595_);
lean_dec(v_a_2593_);
v_a_2596_ = lean_ctor_get(v_fst_2594_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v_fst_2594_, 1);
v_d_2584_ = v_a_2596_;
v___y_2585_ = v_snd_2595_;
goto v___jp_2583_;
}
else
{
lean_object* v_snd_2597_; lean_object* v_a_2598_; lean_object* v___y_2600_; lean_object* v___y_2604_; lean_object* v___x_2630_; 
v_snd_2597_ = lean_ctor_get(v_a_2593_, 1);
lean_inc(v_snd_2597_);
lean_dec(v_a_2593_);
v_a_2598_ = lean_ctor_get(v_fst_2594_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v_fst_2594_, 1);
lean_inc_ref(v___y_2580_);
v___x_2630_ = l_Lean_Environment_find_x3f(v___y_2580_, v_k_2589_, v___x_2577_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_2632_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2631_);
v___y_2604_ = v___x_2632_;
goto v___jp_2603_;
}
else
{
lean_object* v_val_2633_; 
v_val_2633_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2630_, 1);
v___y_2604_ = v_val_2633_;
goto v___jp_2603_;
}
v___jp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_array_push(v_a_2598_, v___y_2600_);
v_init_2578_ = v___x_2601_;
v_x_2579_ = v_r_2591_;
v___y_2581_ = v_snd_2597_;
goto _start;
}
v___jp_2603_:
{
if (lean_obj_tag(v___y_2604_) == 7)
{
lean_object* v_val_2605_; uint8_t v_isUnsafe_2606_; 
v_val_2605_ = lean_ctor_get(v___y_2604_, 0);
lean_inc_ref(v_val_2605_);
lean_dec_ref_known(v___y_2604_, 1);
v_isUnsafe_2606_ = lean_ctor_get_uint8(v_val_2605_, sizeof(void*)*7 + 1);
if (v_isUnsafe_2606_ == 0)
{
v___y_2600_ = v_val_2605_;
goto v___jp_2599_;
}
else
{
if (v___x_2577_ == 0)
{
uint8_t v_exportUnsafe_2607_; 
v_exportUnsafe_2607_ = lean_ctor_get_uint8(v_snd_2597_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v_val_2605_);
lean_dec(v_a_2598_);
v___x_2608_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__2);
v___x_2609_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_2608_, v___y_2580_, v_snd_2597_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v_fst_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v_fst_2611_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_fst_2611_);
if (lean_obj_tag(v_fst_2611_) == 0)
{
lean_object* v_snd_2612_; lean_object* v_a_2613_; 
lean_dec(v_r_2591_);
v_snd_2612_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_snd_2612_);
lean_dec(v_a_2610_);
v_a_2613_ = lean_ctor_get(v_fst_2611_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v_fst_2611_, 1);
v_d_2584_ = v_a_2613_;
v___y_2585_ = v_snd_2612_;
goto v___jp_2583_;
}
else
{
lean_object* v_snd_2614_; lean_object* v_a_2615_; 
v_snd_2614_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_snd_2614_);
lean_dec(v_a_2610_);
v_a_2615_ = lean_ctor_get(v_fst_2611_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v_fst_2611_, 1);
v_init_2578_ = v_a_2615_;
v_x_2579_ = v_r_2591_;
v___y_2581_ = v_snd_2614_;
goto _start;
}
}
else
{
lean_dec(v_r_2591_);
return v___x_2609_;
}
}
else
{
v___y_2600_ = v_val_2605_;
goto v___jp_2599_;
}
}
else
{
v___y_2600_ = v_val_2605_;
goto v___jp_2599_;
}
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec_ref(v___y_2604_);
v___x_2617_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__4);
v___x_2618_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2617_, v___y_2580_, v_snd_2597_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_snd_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_snd_2620_ = lean_ctor_get(v_a_2619_, 1);
lean_inc(v_snd_2620_);
lean_dec(v_a_2619_);
v_init_2578_ = v_a_2598_;
v_x_2579_ = v_r_2591_;
v___y_2581_ = v_snd_2620_;
goto _start;
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2598_);
lean_dec(v_r_2591_);
v_a_2622_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2618_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
}
else
{
lean_dec(v_r_2591_);
lean_dec(v_k_2589_);
return v___x_2592_;
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_init_2578_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___y_2581_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
v___jp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_d_2584_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v___y_2585_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v___x_2637_, lean_object* v_init_2638_, lean_object* v_x_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___x_172041__boxed_2643_; lean_object* v_res_2644_; 
v___x_172041__boxed_2643_ = lean_unbox(v___x_2637_);
v_res_2644_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_172041__boxed_2643_, v_init_2638_, v_x_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2645_, lean_object* v_k_2646_){
_start:
{
if (lean_obj_tag(v_t_2645_) == 0)
{
lean_object* v_k_2647_; lean_object* v_v_2648_; lean_object* v_l_2649_; lean_object* v_r_2650_; uint8_t v___x_2651_; 
v_k_2647_ = lean_ctor_get(v_t_2645_, 1);
v_v_2648_ = lean_ctor_get(v_t_2645_, 2);
v_l_2649_ = lean_ctor_get(v_t_2645_, 3);
v_r_2650_ = lean_ctor_get(v_t_2645_, 4);
v___x_2651_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2646_, v_k_2647_);
switch(v___x_2651_)
{
case 0:
{
v_t_2645_ = v_l_2649_;
goto _start;
}
case 1:
{
lean_object* v___x_2653_; 
lean_inc(v_v_2648_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_v_2648_);
return v___x_2653_;
}
default: 
{
v_t_2645_ = v_r_2650_;
goto _start;
}
}
}
else
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_box(0);
return v___x_2655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2656_, lean_object* v_k_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2656_, v_k_2657_);
lean_dec(v_k_2657_);
lean_dec(v_t_2656_);
return v_res_2658_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Array_instInhabited(lean_box(0));
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___f_2678_; lean_object* v___x_163477__overap_2679_; lean_object* v___x_2680_; 
v___x_2664_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2665_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2665_, 0, v___x_2664_);
v___f_2666_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2666_, 0, v___x_2664_);
v___f_2667_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2667_, 0, v___x_2664_);
v___f_2668_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2668_, 0, v___x_2664_);
v___x_2669_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2669_, 0, lean_box(0));
lean_closure_set(v___x_2669_, 1, lean_box(0));
lean_closure_set(v___x_2669_, 2, v___x_2664_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___f_2665_);
v___x_2671_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2671_, 0, lean_box(0));
lean_closure_set(v___x_2671_, 1, lean_box(0));
lean_closure_set(v___x_2671_, 2, v___x_2664_);
v___x_2672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_ctor_set(v___x_2672_, 2, v___f_2666_);
lean_ctor_set(v___x_2672_, 3, v___f_2667_);
lean_ctor_set(v___x_2672_, 4, v___f_2668_);
v___x_2673_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2673_, 0, lean_box(0));
lean_closure_set(v___x_2673_, 1, lean_box(0));
lean_closure_set(v___x_2673_, 2, v___x_2664_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
v___x_2677_ = l_instInhabitedOfMonad___redArg(v___x_2674_, v___x_2676_);
v___f_2678_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2678_, 0, v___x_2677_);
v___x_163477__overap_2679_ = lean_panic_fn_borrowed(v___f_2678_, v_msg_2660_);
lean_dec_ref(v___f_2678_);
lean_inc_ref(v___y_2661_);
v___x_2680_ = lean_apply_3(v___x_163477__overap_2679_, v___y_2661_, v___y_2662_, lean_box(0));
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2681_, v___y_2682_, v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2685_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2687_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2688_ = lean_unsigned_to_nat(10u);
v___x_2689_ = lean_unsigned_to_nat(334u);
v___x_2690_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2691_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2692_ = l_mkPanicMessageWithDecl(v___x_2691_, v___x_2690_, v___x_2689_, v___x_2688_, v___x_2687_);
return v___x_2692_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2));
v___x_2695_ = lean_unsigned_to_nat(15u);
v___x_2696_ = lean_unsigned_to_nat(336u);
v___x_2697_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_2698_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2699_ = l_mkPanicMessageWithDecl(v___x_2698_, v___x_2697_, v___x_2696_, v___x_2695_, v___x_2694_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2700_, uint8_t v___x_2701_, lean_object* v_as_x27_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
if (lean_obj_tag(v_as_x27_2702_) == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_b_2703_);
lean_ctor_set(v___x_2707_, 1, v___y_2705_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
else
{
lean_object* v_head_2709_; lean_object* v_tail_2710_; lean_object* v___y_2712_; lean_object* v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2752_; lean_object* v___x_2768_; 
v_head_2709_ = lean_ctor_get(v_as_x27_2702_, 0);
v_tail_2710_ = lean_ctor_get(v_as_x27_2702_, 1);
lean_inc(v_head_2709_);
lean_inc_ref(v___y_2704_);
v___x_2768_ = l_Lean_Environment_find_x3f(v___y_2704_, v_head_2709_, v___x_2701_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_2770_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2769_);
v___y_2752_ = v___x_2770_;
goto v___jp_2751_;
}
else
{
lean_object* v_val_2771_; 
v_val_2771_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v___x_2768_, 1);
v___y_2752_ = v_val_2771_;
goto v___jp_2751_;
}
v___jp_2711_:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_array_push(v_b_2703_, v___y_2712_);
v_as_x27_2702_ = v_tail_2710_;
v_b_2703_ = v___x_2713_;
goto _start;
}
v___jp_2715_:
{
if (v___y_2717_ == 0)
{
uint8_t v_exportUnsafe_2718_; 
v_exportUnsafe_2718_ = lean_ctor_get_uint8(v___y_2705_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v___y_2716_);
lean_dec_ref(v_b_2703_);
v___x_2719_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1);
v___x_2720_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2719_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2742_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2742_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2742_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_fst_2725_; 
v_fst_2725_ = lean_ctor_get(v_a_2721_, 0);
lean_inc(v_fst_2725_);
if (lean_obj_tag(v_fst_2725_) == 0)
{
lean_object* v_snd_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2737_; 
v_snd_2726_ = lean_ctor_get(v_a_2721_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; 
v_unused_2738_ = lean_ctor_get(v_a_2721_, 0);
lean_dec(v_unused_2738_);
v___x_2728_ = v_a_2721_;
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snd_2726_);
lean_dec(v_a_2721_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2737_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_a_2730_; lean_object* v___x_2732_; 
v_a_2730_ = lean_ctor_get(v_fst_2725_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v_fst_2725_, 1);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v_a_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_snd_2726_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2732_);
v___x_2734_ = v___x_2723_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_snd_2739_; lean_object* v_a_2740_; 
lean_del_object(v___x_2723_);
v_snd_2739_ = lean_ctor_get(v_a_2721_, 1);
lean_inc(v_snd_2739_);
lean_dec(v_a_2721_);
v_a_2740_ = lean_ctor_get(v_fst_2725_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v_fst_2725_, 1);
v_as_x27_2702_ = v_tail_2710_;
v_b_2703_ = v_a_2740_;
v___y_2705_ = v_snd_2739_;
goto _start;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2743_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2720_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2720_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
v___y_2712_ = v___y_2716_;
goto v___jp_2711_;
}
}
else
{
v___y_2712_ = v___y_2716_;
goto v___jp_2711_;
}
}
v___jp_2751_:
{
if (lean_obj_tag(v___y_2752_) == 6)
{
lean_object* v_val_2753_; uint8_t v_isUnsafe_2754_; 
v_val_2753_ = lean_ctor_get(v___y_2752_, 0);
lean_inc_ref(v_val_2753_);
lean_dec_ref_known(v___y_2752_, 1);
v_isUnsafe_2754_ = lean_ctor_get_uint8(v_val_2753_, sizeof(void*)*5);
if (v_isUnsafe_2754_ == 0)
{
v___y_2716_ = v_val_2753_;
v___y_2717_ = v___y_2700_;
goto v___jp_2715_;
}
else
{
v___y_2716_ = v_val_2753_;
v___y_2717_ = v___x_2701_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec_ref(v___y_2752_);
v___x_2755_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3);
v___x_2756_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2755_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v_snd_2758_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v_snd_2758_ = lean_ctor_get(v_a_2757_, 1);
lean_inc(v_snd_2758_);
lean_dec(v_a_2757_);
v_as_x27_2702_ = v_tail_2710_;
v___y_2705_ = v_snd_2758_;
goto _start;
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v_b_2703_);
v_a_2760_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2756_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2756_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2772_, lean_object* v___x_2773_, lean_object* v_as_x27_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v___y_172292__boxed_2779_; uint8_t v___x_172293__boxed_2780_; lean_object* v_res_2781_; 
v___y_172292__boxed_2779_ = lean_unbox(v___y_2772_);
v___x_172293__boxed_2780_ = lean_unbox(v___x_2773_);
v_res_2781_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172292__boxed_2779_, v___x_172293__boxed_2780_, v_as_x27_2774_, v_b_2775_, v___y_2776_, v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v_as_x27_2774_);
return v_res_2781_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0(void){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Array_instInhabited(lean_box(0));
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___f_2804_; lean_object* v___x_164159__overap_2805_; lean_object* v___x_2806_; 
v___x_2787_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2788_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2788_, 0, v___x_2787_);
v___f_2789_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2789_, 0, v___x_2787_);
v___f_2790_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2790_, 0, v___x_2787_);
v___f_2791_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2791_, 0, v___x_2787_);
v___x_2792_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2792_, 0, lean_box(0));
lean_closure_set(v___x_2792_, 1, lean_box(0));
lean_closure_set(v___x_2792_, 2, v___x_2787_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___f_2788_);
v___x_2794_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2794_, 0, lean_box(0));
lean_closure_set(v___x_2794_, 1, lean_box(0));
lean_closure_set(v___x_2794_, 2, v___x_2787_);
v___x_2795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_ctor_set(v___x_2795_, 2, v___f_2789_);
lean_ctor_set(v___x_2795_, 3, v___f_2790_);
lean_ctor_set(v___x_2795_, 4, v___f_2791_);
v___x_2796_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2796_, 0, lean_box(0));
lean_closure_set(v___x_2796_, 1, lean_box(0));
lean_closure_set(v___x_2796_, 2, v___x_2787_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__11___closed__0);
v___x_2799_ = lean_box(1);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2798_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = l_instInhabitedOfMonad___redArg(v___x_2797_, v___x_2802_);
v___f_2804_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2804_, 0, v___x_2803_);
v___x_164159__overap_2805_ = lean_panic_fn_borrowed(v___f_2804_, v_msg_2783_);
lean_dec_ref(v___f_2804_);
lean_inc_ref(v___y_2784_);
v___x_2806_ = lean_apply_3(v___x_164159__overap_2805_, v___y_2784_, v___y_2785_, lean_box(0));
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2807_, v___y_2808_, v___y_2809_);
lean_dec_ref(v___y_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(size_t v_sz_2812_, size_t v_i_2813_, lean_object* v_bs_2814_){
_start:
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_usize_dec_lt(v_i_2813_, v_sz_2812_);
if (v___x_2815_ == 0)
{
return v_bs_2814_;
}
else
{
lean_object* v_v_2816_; lean_object* v___x_2817_; lean_object* v_bs_x27_2818_; size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v_v_2816_ = lean_array_uget(v_bs_2814_, v_i_2813_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v_bs_x27_2818_ = lean_array_uset(v_bs_2814_, v_i_2813_, v___x_2817_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2813_, v___x_2819_);
v___x_2821_ = lean_array_uset(v_bs_x27_2818_, v_i_2813_, v_v_2816_);
v_i_2813_ = v___x_2820_;
v_bs_2814_ = v___x_2821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25___boxed(lean_object* v_sz_2823_, lean_object* v_i_2824_, lean_object* v_bs_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2823_);
lean_dec(v_sz_2823_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(v_sz_boxed_2826_, v_i_boxed_2827_, v_bs_2825_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(lean_object* v_a_2829_){
_start:
{
size_t v_sz_2830_; size_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_sz_2830_ = lean_array_size(v_a_2829_);
v___x_2831_ = ((size_t)0ULL);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21_spec__25(v_sz_2830_, v___x_2831_, v_a_2829_);
v___x_2833_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_array_mk(v_a_2834_);
v___x_2836_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(lean_object* v_as_2837_, size_t v_sz_2838_, size_t v_i_2839_, lean_object* v_b_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v___x_2844_; 
v___x_2844_ = lean_usize_dec_lt(v_i_2839_, v_sz_2838_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_b_2840_);
lean_ctor_set(v___x_2845_, 1, v___y_2842_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
else
{
lean_object* v_visitedNames_2847_; lean_object* v_visitedLevels_2848_; lean_object* v_visitedExprs_2849_; lean_object* v_visitedConstants_2850_; lean_object* v_noMDataExprs_2851_; uint8_t v_exportMData_2852_; uint8_t v_exportUnsafe_2853_; uint8_t v_ignoreMissing_2854_; lean_object* v_recursorMap_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2874_; 
v_visitedNames_2847_ = lean_ctor_get(v___y_2842_, 0);
v_visitedLevels_2848_ = lean_ctor_get(v___y_2842_, 1);
v_visitedExprs_2849_ = lean_ctor_get(v___y_2842_, 2);
v_visitedConstants_2850_ = lean_ctor_get(v___y_2842_, 3);
v_noMDataExprs_2851_ = lean_ctor_get(v___y_2842_, 4);
v_exportMData_2852_ = lean_ctor_get_uint8(v___y_2842_, sizeof(void*)*6);
v_exportUnsafe_2853_ = lean_ctor_get_uint8(v___y_2842_, sizeof(void*)*6 + 1);
v_ignoreMissing_2854_ = lean_ctor_get_uint8(v___y_2842_, sizeof(void*)*6 + 2);
v_recursorMap_2855_ = lean_ctor_get(v___y_2842_, 5);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___y_2842_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2857_ = v___y_2842_;
v_isShared_2858_ = v_isSharedCheck_2874_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_recursorMap_2855_);
lean_inc(v_noMDataExprs_2851_);
lean_inc(v_visitedConstants_2850_);
lean_inc(v_visitedExprs_2849_);
lean_inc(v_visitedLevels_2848_);
lean_inc(v_visitedNames_2847_);
lean_dec(v___y_2842_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2874_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v_a_2859_; lean_object* v_toConstantVal_2860_; lean_object* v_name_2861_; lean_object* v_type_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v_a_2859_ = lean_array_uget_borrowed(v_as_2837_, v_i_2839_);
v_toConstantVal_2860_ = lean_ctor_get(v_a_2859_, 0);
v_name_2861_ = lean_ctor_get(v_toConstantVal_2860_, 0);
v_type_2862_ = lean_ctor_get(v_toConstantVal_2860_, 2);
lean_inc(v_name_2861_);
v___x_2863_ = l_Lean_NameHashSet_insert(v_visitedConstants_2850_, v_name_2861_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 3, v___x_2863_);
v___x_2865_ = v___x_2857_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_visitedNames_2847_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_visitedLevels_2848_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_visitedExprs_2849_);
lean_ctor_set(v_reuseFailAlloc_2873_, 3, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2873_, 4, v_noMDataExprs_2851_);
lean_ctor_set(v_reuseFailAlloc_2873_, 5, v_recursorMap_2855_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*6, v_exportMData_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*6 + 1, v_exportUnsafe_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*6 + 2, v_ignoreMissing_2854_);
v___x_2865_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; 
lean_inc_ref(v_type_2862_);
v___x_2866_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_2862_, v___y_2841_, v___x_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_snd_2868_; lean_object* v___x_2869_; size_t v___x_2870_; size_t v___x_2871_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v_snd_2868_ = lean_ctor_get(v_a_2867_, 1);
lean_inc(v_snd_2868_);
lean_dec(v_a_2867_);
v___x_2869_ = lean_box(0);
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_add(v_i_2839_, v___x_2870_);
v_i_2839_ = v___x_2871_;
v_b_2840_ = v___x_2869_;
v___y_2842_ = v_snd_2868_;
goto _start;
}
else
{
return v___x_2866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
if (lean_obj_tag(v_as_x27_2875_) == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_b_2876_);
lean_ctor_set(v___x_2880_, 1, v___y_2878_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
else
{
lean_object* v_head_2882_; lean_object* v_tail_2883_; lean_object* v_rhs_2884_; lean_object* v___x_2885_; 
v_head_2882_ = lean_ctor_get(v_as_x27_2875_, 0);
v_tail_2883_ = lean_ctor_get(v_as_x27_2875_, 1);
v_rhs_2884_ = lean_ctor_get(v_head_2882_, 2);
lean_inc_ref(v_rhs_2884_);
v___x_2885_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_2884_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v_snd_2887_; lean_object* v___x_2888_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v_snd_2887_ = lean_ctor_get(v_a_2886_, 1);
lean_inc(v_snd_2887_);
lean_dec(v_a_2886_);
v___x_2888_ = lean_box(0);
v_as_x27_2875_ = v_tail_2883_;
v_b_2876_ = v___x_2888_;
v___y_2878_ = v_snd_2887_;
goto _start;
}
else
{
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(lean_object* v_as_2890_, size_t v_sz_2891_, size_t v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_b_2893_);
lean_ctor_set(v___x_2898_, 1, v___y_2895_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
else
{
lean_object* v_a_2900_; lean_object* v_rules_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2900_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
v_rules_2901_ = lean_ctor_get(v_a_2900_, 6);
v___x_2902_ = lean_box(0);
v___x_2903_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_2901_, v___x_2902_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v_snd_2905_; size_t v___x_2906_; size_t v___x_2907_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v_snd_2905_ = lean_ctor_get(v_a_2904_, 1);
lean_inc(v_snd_2905_);
lean_dec(v_a_2904_);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2892_, v___x_2906_);
v_i_2892_ = v___x_2907_;
v_b_2893_ = v___x_2902_;
v___y_2895_ = v_snd_2905_;
goto _start;
}
else
{
return v___x_2903_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_unsigned_to_nat(16u);
v___x_2911_ = lean_mk_array(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_2913_ = lean_unsigned_to_nat(0u);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_visitedConstants_2941_; lean_object* v_nat_2942_; uint8_t v___x_2943_; 
v_visitedConstants_2941_ = lean_ctor_get(v_a_2935_, 3);
v_nat_2942_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_2943_ = l_Lean_NameHashSet_contains(v_visitedConstants_2941_, v_nat_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_inc_ref(v_a_2934_);
v___x_2944_ = l_Lean_Environment_find_x3f(v_a_2934_, v_nat_2942_, v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
goto v___jp_2937_;
}
else
{
lean_object* v___x_2945_; 
lean_dec_ref_known(v___x_2944_, 1);
v___x_2945_ = l_LeanExport_dumpConstant(v_nat_2942_, v_a_2934_, v_a_2935_);
return v___x_2945_;
}
}
else
{
goto v___jp_2937_;
}
v___jp_2937_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v_a_2935_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___y_2961_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v_visitedConstants_2968_; lean_object* v_visitedConstants_2973_; lean_object* v_charOfNat_2974_; uint8_t v___x_2975_; 
v_visitedConstants_2973_ = lean_ctor_get(v_a_2958_, 3);
v_charOfNat_2974_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_2975_ = l_Lean_NameHashSet_contains(v_visitedConstants_2973_, v_charOfNat_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_inc_ref(v_a_2957_);
v___x_2976_ = l_Lean_Environment_find_x3f(v_a_2957_, v_charOfNat_2974_, v___x_2975_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_inc_ref(v_visitedConstants_2973_);
v___y_2966_ = v_a_2957_;
v___y_2967_ = v_a_2958_;
v_visitedConstants_2968_ = v_visitedConstants_2973_;
goto v___jp_2965_;
}
else
{
lean_object* v___x_2977_; 
lean_dec_ref_known(v___x_2976_, 1);
v___x_2977_ = l_LeanExport_dumpConstant(v_charOfNat_2974_, v_a_2957_, v_a_2958_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v_snd_2979_; lean_object* v_visitedConstants_2980_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v_snd_2979_ = lean_ctor_get(v_a_2978_, 1);
lean_inc(v_snd_2979_);
lean_dec(v_a_2978_);
v_visitedConstants_2980_ = lean_ctor_get(v_snd_2979_, 3);
lean_inc_ref(v_visitedConstants_2980_);
v___y_2966_ = v_a_2957_;
v___y_2967_ = v_snd_2979_;
v_visitedConstants_2968_ = v_visitedConstants_2980_;
goto v___jp_2965_;
}
else
{
return v___x_2977_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_2973_);
v___y_2966_ = v_a_2957_;
v___y_2967_ = v_a_2958_;
v_visitedConstants_2968_ = v_visitedConstants_2973_;
goto v___jp_2965_;
}
v___jp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v___y_2961_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
v___jp_2965_:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_2970_ = l_Lean_NameHashSet_contains(v_visitedConstants_2968_, v___x_2969_);
lean_dec_ref(v_visitedConstants_2968_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_inc_ref(v___y_2966_);
v___x_2971_ = l_Lean_Environment_find_x3f(v___y_2966_, v___x_2969_, v___x_2970_);
if (lean_obj_tag(v___x_2971_) == 0)
{
v___y_2961_ = v___y_2967_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2971_, 1);
v___x_2972_ = l_LeanExport_dumpConstant(v___x_2969_, v___y_2966_, v___y_2967_);
return v___x_2972_;
}
}
else
{
v___y_2961_ = v___y_2967_;
goto v___jp_2960_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2991_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_2992_ = lean_unsigned_to_nat(29u);
v___x_2993_ = lean_unsigned_to_nat(177u);
v___x_2994_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_2995_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2996_ = l_mkPanicMessageWithDecl(v___x_2995_, v___x_2994_, v___x_2993_, v___x_2992_, v___x_2991_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_visitedNames_3001_; lean_object* v_visitedLevels_3002_; lean_object* v_visitedExprs_3003_; lean_object* v_visitedConstants_3004_; lean_object* v_noMDataExprs_3005_; uint8_t v_exportMData_3006_; uint8_t v_exportUnsafe_3007_; uint8_t v_ignoreMissing_3008_; lean_object* v_recursorMap_3009_; lean_object* v___x_3010_; 
v_visitedNames_3001_ = lean_ctor_get(v_a_2999_, 0);
v_visitedLevels_3002_ = lean_ctor_get(v_a_2999_, 1);
v_visitedExprs_3003_ = lean_ctor_get(v_a_2999_, 2);
v_visitedConstants_3004_ = lean_ctor_get(v_a_2999_, 3);
v_noMDataExprs_3005_ = lean_ctor_get(v_a_2999_, 4);
v_exportMData_3006_ = lean_ctor_get_uint8(v_a_2999_, sizeof(void*)*6);
v_exportUnsafe_3007_ = lean_ctor_get_uint8(v_a_2999_, sizeof(void*)*6 + 1);
v_ignoreMissing_3008_ = lean_ctor_get_uint8(v_a_2999_, sizeof(void*)*6 + 2);
v_recursorMap_3009_ = lean_ctor_get(v_a_2999_, 5);
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_3003_, v_e_2997_);
if (lean_obj_tag(v___x_3010_) == 1)
{
lean_object* v_val_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v_e_2997_);
v_val_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3019_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_val_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3019_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v_val_3011_);
lean_ctor_set(v___x_3015_, 1, v_a_2999_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3015_);
v___x_3017_ = v___x_3013_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v_fst_3022_; lean_object* v_visitedNames_3023_; lean_object* v_visitedLevels_3024_; lean_object* v_visitedExprs_3025_; lean_object* v_visitedConstants_3026_; lean_object* v_noMDataExprs_3027_; uint8_t v_exportMData_3028_; uint8_t v_exportUnsafe_3029_; uint8_t v_ignoreMissing_3030_; lean_object* v_recursorMap_3031_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; 
lean_dec(v___x_3010_);
v___x_3020_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_2997_))
{
case 0:
{
lean_object* v_deBruijnIndex_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_inc(v_recursorMap_3009_);
lean_inc_ref(v_noMDataExprs_3005_);
lean_inc_ref(v_visitedConstants_3004_);
lean_inc_ref(v_visitedExprs_3003_);
lean_inc_ref(v_visitedLevels_3002_);
lean_inc_ref(v_visitedNames_3001_);
lean_dec_ref(v_a_2999_);
v_deBruijnIndex_3069_ = lean_ctor_get(v_e_2997_, 0);
v___x_3070_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3069_);
v___x_3071_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3069_);
v___x_3072_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3070_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_Json_mkObj(v___x_3075_);
lean_dec_ref_known(v___x_3075_, 2);
v_fst_3022_ = v___x_3076_;
v_visitedNames_3023_ = v_visitedNames_3001_;
v_visitedLevels_3024_ = v_visitedLevels_3002_;
v_visitedExprs_3025_ = v_visitedExprs_3003_;
v_visitedConstants_3026_ = v_visitedConstants_3004_;
v_noMDataExprs_3027_ = v_noMDataExprs_3005_;
v_exportMData_3028_ = v_exportMData_3006_;
v_exportUnsafe_3029_ = v_exportUnsafe_3007_;
v_ignoreMissing_3030_ = v_ignoreMissing_3008_;
v_recursorMap_3031_ = v_recursorMap_3009_;
goto v___jp_3021_;
}
case 3:
{
lean_object* v_u_3077_; lean_object* v___x_3078_; 
v_u_3077_ = lean_ctor_get(v_e_2997_, 0);
lean_inc(v_u_3077_);
v___x_3078_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3077_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3100_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3100_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3100_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v_fst_3083_; lean_object* v_snd_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3099_; 
v_fst_3083_ = lean_ctor_get(v_a_3079_, 0);
v_snd_3084_ = lean_ctor_get(v_a_3079_, 1);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_a_3079_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3086_ = v_a_3079_;
v_isShared_3087_ = v_isSharedCheck_3099_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_snd_3084_);
lean_inc(v_fst_3083_);
lean_dec(v_a_3079_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3099_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3088_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3089_ = l_Lean_JsonNumber_fromNat(v_fst_3083_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 2);
lean_ctor_set(v___x_3081_, 0, v___x_3089_);
v___x_3091_ = v___x_3081_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 1, v___x_3091_);
lean_ctor_set(v___x_3086_, 0, v___x_3088_);
v___x_3093_ = v___x_3086_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_box(0);
v___x_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = l_Lean_Json_mkObj(v___x_3095_);
lean_dec_ref_known(v___x_3095_, 2);
v_fst_3058_ = v___x_3096_;
v_snd_3059_ = v_snd_3084_;
goto v___jp_3057_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 1);
return v___x_3078_;
}
}
case 4:
{
lean_object* v_declName_3101_; lean_object* v_us_3102_; lean_object* v___x_3103_; 
v_declName_3101_ = lean_ctor_get(v_e_2997_, 0);
v_us_3102_ = lean_ctor_get(v_e_2997_, 1);
lean_inc(v_declName_3101_);
v___x_3103_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3101_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3151_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3151_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3151_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3150_; 
v_fst_3108_ = lean_ctor_get(v_a_3104_, 0);
v_snd_3109_ = lean_ctor_get(v_a_3104_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_3104_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3111_ = v_a_3104_;
v_isShared_3112_ = v_isSharedCheck_3150_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_snd_3109_);
lean_inc(v_fst_3108_);
lean_dec(v_a_3104_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3150_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_box(0);
lean_inc(v_us_3102_);
v___x_3114_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3102_, v___x_3113_, v_a_2998_, v_snd_3109_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v_fst_3116_; lean_object* v_snd_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3141_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v_fst_3116_ = lean_ctor_get(v_a_3115_, 0);
v_snd_3117_ = lean_ctor_get(v_a_3115_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_a_3115_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3119_ = v_a_3115_;
v_isShared_3120_ = v_isSharedCheck_3141_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_snd_3117_);
lean_inc(v_fst_3116_);
lean_dec(v_a_3115_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3141_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3121_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3123_ = l_Lean_JsonNumber_fromNat(v_fst_3108_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 2);
lean_ctor_set(v___x_3106_, 0, v___x_3123_);
v___x_3125_ = v___x_3106_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v___x_3125_);
lean_ctor_set(v___x_3119_, 0, v___x_3122_);
v___x_3127_ = v___x_3119_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3128_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3129_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3116_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3129_);
lean_ctor_set(v___x_3111_, 0, v___x_3128_);
v___x_3131_ = v___x_3111_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3113_);
v___x_3133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3127_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = l_Lean_Json_mkObj(v___x_3133_);
lean_dec_ref_known(v___x_3133_, 2);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3121_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
lean_ctor_set(v___x_3136_, 1, v___x_3113_);
v___x_3137_ = l_Lean_Json_mkObj(v___x_3136_);
lean_dec_ref_known(v___x_3136_, 2);
v_fst_3058_ = v___x_3137_;
v_snd_3059_ = v_snd_3117_;
goto v___jp_3057_;
}
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_del_object(v___x_3111_);
lean_dec(v_fst_3108_);
lean_del_object(v___x_3106_);
lean_dec_ref_known(v_e_2997_, 2);
v_a_3142_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3114_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3114_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 2);
return v___x_3103_;
}
}
case 5:
{
lean_object* v_fn_3152_; lean_object* v_arg_3153_; lean_object* v___x_3154_; 
v_fn_3152_ = lean_ctor_get(v_e_2997_, 0);
v_arg_3153_ = lean_ctor_get(v_e_2997_, 1);
lean_inc_ref(v_fn_3152_);
v___x_3154_ = l_LeanExport_dumpExprAux(v_fn_3152_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3201_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3201_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3201_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_fst_3159_; lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3200_; 
v_fst_3159_ = lean_ctor_get(v_a_3155_, 0);
v_snd_3160_ = lean_ctor_get(v_a_3155_, 1);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_a_3155_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3162_ = v_a_3155_;
v_isShared_3163_ = v_isSharedCheck_3200_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_inc(v_fst_3159_);
lean_dec(v_a_3155_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3200_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; 
lean_inc_ref(v_arg_3153_);
v___x_3164_ = l_LeanExport_dumpExprAux(v_arg_3153_, v_a_2998_, v_snd_3160_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3199_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3199_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3199_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3198_; 
v_fst_3169_ = lean_ctor_get(v_a_3165_, 0);
v_snd_3170_ = lean_ctor_get(v_a_3165_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_a_3165_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3172_ = v_a_3165_;
v_isShared_3173_ = v_isSharedCheck_3198_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_snd_3170_);
lean_inc(v_fst_3169_);
lean_dec(v_a_3165_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3198_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3174_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3175_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3176_ = l_Lean_JsonNumber_fromNat(v_fst_3159_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set_tag(v___x_3167_, 2);
lean_ctor_set(v___x_3167_, 0, v___x_3176_);
v___x_3178_ = v___x_3167_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3180_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v___x_3178_);
lean_ctor_set(v___x_3172_, 0, v___x_3175_);
v___x_3180_ = v___x_3172_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3181_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3182_ = l_Lean_JsonNumber_fromNat(v_fst_3169_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 2);
lean_ctor_set(v___x_3157_, 0, v___x_3182_);
v___x_3184_ = v___x_3157_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3186_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3184_);
lean_ctor_set(v___x_3162_, 0, v___x_3181_);
v___x_3186_ = v___x_3162_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3186_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3180_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_Json_mkObj(v___x_3189_);
lean_dec_ref_known(v___x_3189_, 2);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3174_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___x_3187_);
v___x_3193_ = l_Lean_Json_mkObj(v___x_3192_);
lean_dec_ref_known(v___x_3192_, 2);
v_fst_3058_ = v___x_3193_;
v_snd_3059_ = v_snd_3170_;
goto v___jp_3057_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3162_);
lean_dec(v_fst_3159_);
lean_del_object(v___x_3157_);
lean_dec_ref_known(v_e_2997_, 2);
return v___x_3164_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 2);
return v___x_3154_;
}
}
case 6:
{
lean_object* v_binderName_3202_; lean_object* v_binderType_3203_; lean_object* v_body_3204_; uint8_t v_binderInfo_3205_; lean_object* v___x_3206_; 
v_binderName_3202_ = lean_ctor_get(v_e_2997_, 0);
v_binderType_3203_ = lean_ctor_get(v_e_2997_, 1);
v_body_3204_ = lean_ctor_get(v_e_2997_, 2);
v_binderInfo_3205_ = lean_ctor_get_uint8(v_e_2997_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3202_);
v___x_3206_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3202_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3278_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3278_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3278_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3277_; 
v_fst_3211_ = lean_ctor_get(v_a_3207_, 0);
v_snd_3212_ = lean_ctor_get(v_a_3207_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_a_3207_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3214_ = v_a_3207_;
v_isShared_3215_ = v_isSharedCheck_3277_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snd_3212_);
lean_inc(v_fst_3211_);
lean_dec(v_a_3207_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3277_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; 
lean_inc_ref(v_binderType_3203_);
v___x_3216_ = l_LeanExport_dumpExprAux(v_binderType_3203_, v_a_2998_, v_snd_3212_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3276_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3276_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3276_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v_fst_3221_; lean_object* v_snd_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3275_; 
v_fst_3221_ = lean_ctor_get(v_a_3217_, 0);
v_snd_3222_ = lean_ctor_get(v_a_3217_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_a_3217_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3224_ = v_a_3217_;
v_isShared_3225_ = v_isSharedCheck_3275_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snd_3222_);
lean_inc(v_fst_3221_);
lean_dec(v_a_3217_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3275_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; 
lean_inc_ref(v_body_3204_);
v___x_3226_ = l_LeanExport_dumpExprAux(v_body_3204_, v_a_2998_, v_snd_3222_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3274_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3274_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3274_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_fst_3231_; lean_object* v_snd_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3273_; 
v_fst_3231_ = lean_ctor_get(v_a_3227_, 0);
v_snd_3232_ = lean_ctor_get(v_a_3227_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_a_3227_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3234_ = v_a_3227_;
v_isShared_3235_ = v_isSharedCheck_3273_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snd_3232_);
lean_inc(v_fst_3231_);
lean_dec(v_a_3227_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3273_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3236_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3238_ = l_Lean_JsonNumber_fromNat(v_fst_3211_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 2);
lean_ctor_set(v___x_3229_, 0, v___x_3238_);
v___x_3240_ = v___x_3229_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 1, v___x_3240_);
lean_ctor_set(v___x_3234_, 0, v___x_3237_);
v___x_3242_ = v___x_3234_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3244_ = l_Lean_JsonNumber_fromNat(v_fst_3221_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set_tag(v___x_3219_, 2);
lean_ctor_set(v___x_3219_, 0, v___x_3244_);
v___x_3246_ = v___x_3219_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v___x_3246_);
lean_ctor_set(v___x_3224_, 0, v___x_3243_);
v___x_3248_ = v___x_3224_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3249_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3250_ = l_Lean_JsonNumber_fromNat(v_fst_3231_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 2);
lean_ctor_set(v___x_3209_, 0, v___x_3250_);
v___x_3252_ = v___x_3209_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v___x_3252_);
lean_ctor_set(v___x_3214_, 0, v___x_3249_);
v___x_3254_ = v___x_3214_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3255_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3256_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3205_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3257_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3254_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3248_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3242_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Lean_Json_mkObj(v___x_3262_);
lean_dec_ref_known(v___x_3262_, 2);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3236_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3258_);
v___x_3266_ = l_Lean_Json_mkObj(v___x_3265_);
lean_dec_ref_known(v___x_3265_, 2);
v_fst_3058_ = v___x_3266_;
v_snd_3059_ = v_snd_3232_;
goto v___jp_3057_;
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
lean_del_object(v___x_3224_);
lean_dec(v_fst_3221_);
lean_del_object(v___x_3219_);
lean_del_object(v___x_3214_);
lean_dec(v_fst_3211_);
lean_del_object(v___x_3209_);
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3226_;
}
}
}
}
else
{
lean_del_object(v___x_3214_);
lean_dec(v_fst_3211_);
lean_del_object(v___x_3209_);
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3216_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3206_;
}
}
case 7:
{
lean_object* v_binderName_3279_; lean_object* v_binderType_3280_; lean_object* v_body_3281_; uint8_t v_binderInfo_3282_; lean_object* v___x_3283_; 
v_binderName_3279_ = lean_ctor_get(v_e_2997_, 0);
v_binderType_3280_ = lean_ctor_get(v_e_2997_, 1);
v_body_3281_ = lean_ctor_get(v_e_2997_, 2);
v_binderInfo_3282_ = lean_ctor_get_uint8(v_e_2997_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3279_);
v___x_3283_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3279_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3355_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3355_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3355_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3354_; 
v_fst_3288_ = lean_ctor_get(v_a_3284_, 0);
v_snd_3289_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3291_ = v_a_3284_;
v_isShared_3292_ = v_isSharedCheck_3354_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snd_3289_);
lean_inc(v_fst_3288_);
lean_dec(v_a_3284_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3354_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; 
lean_inc_ref(v_binderType_3280_);
v___x_3293_ = l_LeanExport_dumpExprAux(v_binderType_3280_, v_a_2998_, v_snd_3289_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3353_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3353_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3353_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_fst_3298_; lean_object* v_snd_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3352_; 
v_fst_3298_ = lean_ctor_get(v_a_3294_, 0);
v_snd_3299_ = lean_ctor_get(v_a_3294_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_a_3294_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3301_ = v_a_3294_;
v_isShared_3302_ = v_isSharedCheck_3352_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_snd_3299_);
lean_inc(v_fst_3298_);
lean_dec(v_a_3294_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3352_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; 
lean_inc_ref(v_body_3281_);
v___x_3303_ = l_LeanExport_dumpExprAux(v_body_3281_, v_a_2998_, v_snd_3299_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3351_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3351_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3351_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3350_; 
v_fst_3308_ = lean_ctor_get(v_a_3304_, 0);
v_snd_3309_ = lean_ctor_get(v_a_3304_, 1);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_a_3304_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3311_ = v_a_3304_;
v_isShared_3312_ = v_isSharedCheck_3350_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_snd_3309_);
lean_inc(v_fst_3308_);
lean_dec(v_a_3304_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3350_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3313_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3315_ = l_Lean_JsonNumber_fromNat(v_fst_3288_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 2);
lean_ctor_set(v___x_3306_, 0, v___x_3315_);
v___x_3317_ = v___x_3306_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v___x_3317_);
lean_ctor_set(v___x_3311_, 0, v___x_3314_);
v___x_3319_ = v___x_3311_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
v___x_3320_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3321_ = l_Lean_JsonNumber_fromNat(v_fst_3298_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 2);
lean_ctor_set(v___x_3296_, 0, v___x_3321_);
v___x_3323_ = v___x_3296_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3325_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v___x_3323_);
lean_ctor_set(v___x_3301_, 0, v___x_3320_);
v___x_3325_ = v___x_3301_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3326_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3327_ = l_Lean_JsonNumber_fromNat(v_fst_3308_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 2);
lean_ctor_set(v___x_3286_, 0, v___x_3327_);
v___x_3329_ = v___x_3286_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3331_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3329_);
lean_ctor_set(v___x_3291_, 0, v___x_3326_);
v___x_3331_ = v___x_3291_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3332_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3333_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3282_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3331_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3325_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3319_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_Json_mkObj(v___x_3339_);
lean_dec_ref_known(v___x_3339_, 2);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3313_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v___x_3335_);
v___x_3343_ = l_Lean_Json_mkObj(v___x_3342_);
lean_dec_ref_known(v___x_3342_, 2);
v_fst_3058_ = v___x_3343_;
v_snd_3059_ = v_snd_3309_;
goto v___jp_3057_;
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
lean_del_object(v___x_3301_);
lean_dec(v_fst_3298_);
lean_del_object(v___x_3296_);
lean_del_object(v___x_3291_);
lean_dec(v_fst_3288_);
lean_del_object(v___x_3286_);
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3303_;
}
}
}
}
else
{
lean_del_object(v___x_3291_);
lean_dec(v_fst_3288_);
lean_del_object(v___x_3286_);
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3293_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3283_;
}
}
case 8:
{
lean_object* v_declName_3356_; lean_object* v_type_3357_; lean_object* v_value_3358_; lean_object* v_body_3359_; uint8_t v_nondep_3360_; lean_object* v___x_3361_; 
v_declName_3356_ = lean_ctor_get(v_e_2997_, 0);
v_type_3357_ = lean_ctor_get(v_e_2997_, 1);
v_value_3358_ = lean_ctor_get(v_e_2997_, 2);
v_body_3359_ = lean_ctor_get(v_e_2997_, 3);
v_nondep_3360_ = lean_ctor_get_uint8(v_e_2997_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3356_);
v___x_3361_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3356_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3454_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3454_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3454_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3453_; 
v_fst_3366_ = lean_ctor_get(v_a_3362_, 0);
v_snd_3367_ = lean_ctor_get(v_a_3362_, 1);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_a_3362_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3369_ = v_a_3362_;
v_isShared_3370_ = v_isSharedCheck_3453_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_inc(v_fst_3366_);
lean_dec(v_a_3362_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3453_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; 
lean_inc_ref(v_type_3357_);
v___x_3371_ = l_LeanExport_dumpExprAux(v_type_3357_, v_a_2998_, v_snd_3367_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3452_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3452_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3452_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3451_; 
v_fst_3376_ = lean_ctor_get(v_a_3372_, 0);
v_snd_3377_ = lean_ctor_get(v_a_3372_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3379_ = v_a_3372_;
v_isShared_3380_ = v_isSharedCheck_3451_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_snd_3377_);
lean_inc(v_fst_3376_);
lean_dec(v_a_3372_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3451_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; 
lean_inc_ref(v_value_3358_);
v___x_3381_ = l_LeanExport_dumpExprAux(v_value_3358_, v_a_2998_, v_snd_3377_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3450_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3450_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3450_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_fst_3386_; lean_object* v_snd_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3449_; 
v_fst_3386_ = lean_ctor_get(v_a_3382_, 0);
v_snd_3387_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3389_ = v_a_3382_;
v_isShared_3390_ = v_isSharedCheck_3449_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_snd_3387_);
lean_inc(v_fst_3386_);
lean_dec(v_a_3382_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3449_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; 
lean_inc_ref(v_body_3359_);
v___x_3391_ = l_LeanExport_dumpExprAux(v_body_3359_, v_a_2998_, v_snd_3387_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3448_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3448_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3448_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v_fst_3396_; lean_object* v_snd_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3447_; 
v_fst_3396_ = lean_ctor_get(v_a_3392_, 0);
v_snd_3397_ = lean_ctor_get(v_a_3392_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_a_3392_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3399_ = v_a_3392_;
v_isShared_3400_ = v_isSharedCheck_3447_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_snd_3397_);
lean_inc(v_fst_3396_);
lean_dec(v_a_3392_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3447_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3401_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3403_ = l_Lean_JsonNumber_fromNat(v_fst_3366_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 2);
lean_ctor_set(v___x_3394_, 0, v___x_3403_);
v___x_3405_ = v___x_3394_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
lean_object* v___x_3407_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 1, v___x_3405_);
lean_ctor_set(v___x_3399_, 0, v___x_3402_);
v___x_3407_ = v___x_3399_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3408_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3409_ = l_Lean_JsonNumber_fromNat(v_fst_3376_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set_tag(v___x_3384_, 2);
lean_ctor_set(v___x_3384_, 0, v___x_3409_);
v___x_3411_ = v___x_3384_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3409_);
v___x_3411_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 1, v___x_3411_);
lean_ctor_set(v___x_3389_, 0, v___x_3408_);
v___x_3413_ = v___x_3389_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3414_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3415_ = l_Lean_JsonNumber_fromNat(v_fst_3386_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 2);
lean_ctor_set(v___x_3374_, 0, v___x_3415_);
v___x_3417_ = v___x_3374_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v___x_3417_);
lean_ctor_set(v___x_3379_, 0, v___x_3414_);
v___x_3419_ = v___x_3379_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3420_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3421_ = l_Lean_JsonNumber_fromNat(v_fst_3396_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 2);
lean_ctor_set(v___x_3364_, 0, v___x_3421_);
v___x_3423_ = v___x_3364_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3425_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v___x_3423_);
lean_ctor_set(v___x_3369_, 0, v___x_3420_);
v___x_3425_ = v___x_3369_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3426_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3427_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3427_, 0, v_nondep_3360_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_box(0);
v___x_3430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3425_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3419_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3413_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3407_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_Json_mkObj(v___x_3434_);
lean_dec_ref_known(v___x_3434_, 2);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3401_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v___x_3429_);
v___x_3438_ = l_Lean_Json_mkObj(v___x_3437_);
lean_dec_ref_known(v___x_3437_, 2);
v_fst_3058_ = v___x_3438_;
v_snd_3059_ = v_snd_3397_;
goto v___jp_3057_;
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
lean_del_object(v___x_3389_);
lean_dec(v_fst_3386_);
lean_del_object(v___x_3384_);
lean_del_object(v___x_3379_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3369_);
lean_dec(v_fst_3366_);
lean_del_object(v___x_3364_);
lean_dec_ref_known(v_e_2997_, 4);
return v___x_3391_;
}
}
}
}
else
{
lean_del_object(v___x_3379_);
lean_dec(v_fst_3376_);
lean_del_object(v___x_3374_);
lean_del_object(v___x_3369_);
lean_dec(v_fst_3366_);
lean_del_object(v___x_3364_);
lean_dec_ref_known(v_e_2997_, 4);
return v___x_3381_;
}
}
}
}
else
{
lean_del_object(v___x_3369_);
lean_dec(v_fst_3366_);
lean_del_object(v___x_3364_);
lean_dec_ref_known(v_e_2997_, 4);
return v___x_3371_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 4);
return v___x_3361_;
}
}
case 9:
{
lean_object* v_a_3455_; 
v_a_3455_ = lean_ctor_get(v_e_2997_, 0);
lean_inc_ref(v_a_3455_);
if (lean_obj_tag(v_a_3455_) == 0)
{
lean_object* v_val_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3487_; 
v_val_3456_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3458_ = v_a_3455_;
v_isShared_3459_ = v_isSharedCheck_3487_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_val_3456_);
lean_dec(v_a_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3487_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; 
v___x_3460_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_snd_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3477_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v_snd_3462_ = lean_ctor_get(v_a_3461_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3461_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_a_3461_, 0);
lean_dec(v_unused_3478_);
v___x_3464_ = v_a_3461_;
v_isShared_3465_ = v_isSharedCheck_3477_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_snd_3462_);
lean_dec(v_a_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3477_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3466_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3467_ = l_Nat_reprFast(v_val_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 3);
lean_ctor_set(v___x_3458_, 0, v___x_3467_);
v___x_3469_ = v___x_3458_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v___x_3469_);
lean_ctor_set(v___x_3464_, 0, v___x_3466_);
v___x_3471_ = v___x_3464_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_Json_mkObj(v___x_3473_);
lean_dec_ref_known(v___x_3473_, 2);
v_fst_3058_ = v___x_3474_;
v_snd_3059_ = v_snd_3462_;
goto v___jp_3057_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3458_);
lean_dec(v_val_3456_);
lean_dec_ref_known(v_e_2997_, 1);
v_a_3479_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3460_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3460_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v_val_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3518_; 
v_val_3488_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3490_ = v_a_3455_;
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_val_3488_);
lean_dec(v_a_3455_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; 
v___x_3492_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v_snd_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3508_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v_snd_3494_ = lean_ctor_get(v_a_3493_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_a_3493_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; 
v_unused_3509_ = lean_ctor_get(v_a_3493_, 0);
lean_dec(v_unused_3509_);
v___x_3496_ = v_a_3493_;
v_isShared_3497_ = v_isSharedCheck_3508_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_snd_3494_);
lean_dec(v_a_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3508_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3491_ == 0)
{
lean_ctor_set_tag(v___x_3490_, 3);
v___x_3500_ = v___x_3490_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_val_3488_);
v___x_3500_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v___x_3500_);
lean_ctor_set(v___x_3496_, 0, v___x_3498_);
v___x_3502_ = v___x_3496_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = l_Lean_Json_mkObj(v___x_3504_);
lean_dec_ref_known(v___x_3504_, 2);
v_fst_3058_ = v___x_3505_;
v_snd_3059_ = v_snd_3494_;
goto v___jp_3057_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_del_object(v___x_3490_);
lean_dec_ref(v_val_3488_);
lean_dec_ref_known(v_e_2997_, 1);
v_a_3510_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3492_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3492_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3519_; lean_object* v_expr_3520_; lean_object* v___x_3521_; 
v_data_3519_ = lean_ctor_get(v_e_2997_, 0);
v_expr_3520_ = lean_ctor_get(v_e_2997_, 1);
lean_inc_ref(v_expr_3520_);
v___x_3521_ = l_LeanExport_dumpExprAux(v_expr_3520_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3551_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3551_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3551_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_fst_3526_; lean_object* v_snd_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3550_; 
v_fst_3526_ = lean_ctor_get(v_a_3522_, 0);
v_snd_3527_ = lean_ctor_get(v_a_3522_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_a_3522_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3529_ = v_a_3522_;
v_isShared_3530_ = v_isSharedCheck_3550_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_snd_3527_);
lean_inc(v_fst_3526_);
lean_dec(v_a_3522_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3550_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3531_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3532_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3519_);
v___x_3533_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3519_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 1, v___x_3533_);
lean_ctor_set(v___x_3529_, 0, v___x_3532_);
v___x_3535_ = v___x_3529_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3536_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3537_ = l_Lean_JsonNumber_fromNat(v_fst_3526_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set_tag(v___x_3524_, 2);
lean_ctor_set(v___x_3524_, 0, v___x_3537_);
v___x_3539_ = v___x_3524_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3536_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3535_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Lean_Json_mkObj(v___x_3543_);
lean_dec_ref_known(v___x_3543_, 2);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3531_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v___x_3541_);
v___x_3547_ = l_Lean_Json_mkObj(v___x_3546_);
lean_dec_ref_known(v___x_3546_, 2);
v_fst_3058_ = v___x_3547_;
v_snd_3059_ = v_snd_3527_;
goto v___jp_3057_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 2);
return v___x_3521_;
}
}
case 11:
{
lean_object* v_typeName_3552_; lean_object* v_idx_3553_; lean_object* v_struct_3554_; lean_object* v___x_3555_; 
v_typeName_3552_ = lean_ctor_get(v_e_2997_, 0);
v_idx_3553_ = lean_ctor_get(v_e_2997_, 1);
v_struct_3554_ = lean_ctor_get(v_e_2997_, 2);
lean_inc(v_typeName_3552_);
v___x_3555_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3552_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3607_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3607_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3607_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_fst_3560_; lean_object* v_snd_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3606_; 
v_fst_3560_ = lean_ctor_get(v_a_3556_, 0);
v_snd_3561_ = lean_ctor_get(v_a_3556_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3563_ = v_a_3556_;
v_isShared_3564_ = v_isSharedCheck_3606_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snd_3561_);
lean_inc(v_fst_3560_);
lean_dec(v_a_3556_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3606_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; 
lean_inc_ref(v_struct_3554_);
v___x_3565_ = l_LeanExport_dumpExprAux(v_struct_3554_, v_a_2998_, v_snd_3561_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3605_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3568_ = v___x_3565_;
v_isShared_3569_ = v_isSharedCheck_3605_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3565_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3605_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v_fst_3570_; lean_object* v_snd_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3604_; 
v_fst_3570_ = lean_ctor_get(v_a_3566_, 0);
v_snd_3571_ = lean_ctor_get(v_a_3566_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3566_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3573_ = v_a_3566_;
v_isShared_3574_ = v_isSharedCheck_3604_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_snd_3571_);
lean_inc(v_fst_3570_);
lean_dec(v_a_3566_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3604_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3575_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3576_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3577_ = l_Lean_JsonNumber_fromNat(v_fst_3560_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set_tag(v___x_3568_, 2);
lean_ctor_set(v___x_3568_, 0, v___x_3577_);
v___x_3579_ = v___x_3568_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3579_);
lean_ctor_set(v___x_3573_, 0, v___x_3576_);
v___x_3581_ = v___x_3573_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3582_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3553_);
v___x_3583_ = l_Lean_JsonNumber_fromNat(v_idx_3553_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set_tag(v___x_3558_, 2);
lean_ctor_set(v___x_3558_, 0, v___x_3583_);
v___x_3585_ = v___x_3558_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3585_);
lean_ctor_set(v___x_3563_, 0, v___x_3582_);
v___x_3587_ = v___x_3563_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3588_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3589_ = l_Lean_JsonNumber_fromNat(v_fst_3570_);
v___x_3590_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3588_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = lean_box(0);
v___x_3593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3587_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3581_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = l_Lean_Json_mkObj(v___x_3595_);
lean_dec_ref_known(v___x_3595_, 2);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3575_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set(v___x_3598_, 1, v___x_3592_);
v___x_3599_ = l_Lean_Json_mkObj(v___x_3598_);
lean_dec_ref_known(v___x_3598_, 2);
v_fst_3058_ = v___x_3599_;
v_snd_3059_ = v_snd_3571_;
goto v___jp_3057_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3563_);
lean_dec(v_fst_3560_);
lean_del_object(v___x_3558_);
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3565_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2997_, 3);
return v___x_3555_;
}
}
default: 
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3609_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3608_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v_fst_3611_; lean_object* v_snd_3612_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v_fst_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc(v_fst_3611_);
v_snd_3612_ = lean_ctor_get(v_a_3610_, 1);
lean_inc(v_snd_3612_);
lean_dec(v_a_3610_);
v_fst_3058_ = v_fst_3611_;
v_snd_3059_ = v_snd_3612_;
goto v___jp_3057_;
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v_e_2997_);
v_a_3613_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3609_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3609_);
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
v___jp_3021_:
{
lean_object* v_size_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_size_3032_ = lean_ctor_get(v_visitedExprs_3025_, 0);
lean_inc_n(v_size_3032_, 2);
v___x_3033_ = l_Lean_JsonNumber_fromNat(v_size_3032_);
v___x_3034_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = l_Lean_Json_setObjVal_x21(v_fst_3022_, v___x_3020_, v___x_3034_);
v___x_3036_ = l_Lean_Json_compress(v___x_3035_);
v___x_3037_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3047_; 
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3037_, 0);
lean_dec(v_unused_3048_);
v___x_3039_ = v___x_3037_;
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v___x_3037_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_inc(v_size_3032_);
v___x_3041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3025_, v_e_2997_, v_size_3032_);
v___x_3042_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3042_, 0, v_visitedNames_3023_);
lean_ctor_set(v___x_3042_, 1, v_visitedLevels_3024_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
lean_ctor_set(v___x_3042_, 3, v_visitedConstants_3026_);
lean_ctor_set(v___x_3042_, 4, v_noMDataExprs_3027_);
lean_ctor_set(v___x_3042_, 5, v_recursorMap_3031_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*6, v_exportMData_3028_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*6 + 1, v_exportUnsafe_3029_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*6 + 2, v_ignoreMissing_3030_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_size_3032_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3043_);
v___x_3045_ = v___x_3039_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_size_3032_);
lean_dec(v_recursorMap_3031_);
lean_dec_ref(v_noMDataExprs_3027_);
lean_dec_ref(v_visitedConstants_3026_);
lean_dec_ref(v_visitedExprs_3025_);
lean_dec_ref(v_visitedLevels_3024_);
lean_dec_ref(v_visitedNames_3023_);
lean_dec_ref(v_e_2997_);
v_a_3049_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3037_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3037_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
v___jp_3057_:
{
lean_object* v_visitedNames_3060_; lean_object* v_visitedLevels_3061_; lean_object* v_visitedExprs_3062_; lean_object* v_visitedConstants_3063_; lean_object* v_noMDataExprs_3064_; uint8_t v_exportMData_3065_; uint8_t v_exportUnsafe_3066_; uint8_t v_ignoreMissing_3067_; lean_object* v_recursorMap_3068_; 
v_visitedNames_3060_ = lean_ctor_get(v_snd_3059_, 0);
lean_inc_ref(v_visitedNames_3060_);
v_visitedLevels_3061_ = lean_ctor_get(v_snd_3059_, 1);
lean_inc_ref(v_visitedLevels_3061_);
v_visitedExprs_3062_ = lean_ctor_get(v_snd_3059_, 2);
lean_inc_ref(v_visitedExprs_3062_);
v_visitedConstants_3063_ = lean_ctor_get(v_snd_3059_, 3);
lean_inc_ref(v_visitedConstants_3063_);
v_noMDataExprs_3064_ = lean_ctor_get(v_snd_3059_, 4);
lean_inc_ref(v_noMDataExprs_3064_);
v_exportMData_3065_ = lean_ctor_get_uint8(v_snd_3059_, sizeof(void*)*6);
v_exportUnsafe_3066_ = lean_ctor_get_uint8(v_snd_3059_, sizeof(void*)*6 + 1);
v_ignoreMissing_3067_ = lean_ctor_get_uint8(v_snd_3059_, sizeof(void*)*6 + 2);
v_recursorMap_3068_ = lean_ctor_get(v_snd_3059_, 5);
lean_inc(v_recursorMap_3068_);
lean_dec_ref(v_snd_3059_);
v_fst_3022_ = v_fst_3058_;
v_visitedNames_3023_ = v_visitedNames_3060_;
v_visitedLevels_3024_ = v_visitedLevels_3061_;
v_visitedExprs_3025_ = v_visitedExprs_3062_;
v_visitedConstants_3026_ = v_visitedConstants_3063_;
v_noMDataExprs_3027_ = v_noMDataExprs_3064_;
v_exportMData_3028_ = v_exportMData_3065_;
v_exportUnsafe_3029_ = v_exportUnsafe_3066_;
v_ignoreMissing_3030_ = v_ignoreMissing_3067_;
v_recursorMap_3031_ = v_recursorMap_3068_;
goto v___jp_3021_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
uint8_t v_exportMData_3625_; 
v_exportMData_3625_ = lean_ctor_get_uint8(v_a_3623_, sizeof(void*)*6);
if (v_exportMData_3625_ == 0)
{
lean_object* v_visitedNames_3626_; lean_object* v_visitedLevels_3627_; lean_object* v_visitedExprs_3628_; lean_object* v_visitedConstants_3629_; uint8_t v_exportUnsafe_3630_; uint8_t v_ignoreMissing_3631_; lean_object* v_recursorMap_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3653_; 
v_visitedNames_3626_ = lean_ctor_get(v_a_3623_, 0);
v_visitedLevels_3627_ = lean_ctor_get(v_a_3623_, 1);
v_visitedExprs_3628_ = lean_ctor_get(v_a_3623_, 2);
v_visitedConstants_3629_ = lean_ctor_get(v_a_3623_, 3);
v_exportUnsafe_3630_ = lean_ctor_get_uint8(v_a_3623_, sizeof(void*)*6 + 1);
v_ignoreMissing_3631_ = lean_ctor_get_uint8(v_a_3623_, sizeof(void*)*6 + 2);
v_recursorMap_3632_ = lean_ctor_get(v_a_3623_, 5);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3623_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v_a_3623_, 4);
lean_dec(v_unused_3654_);
v___x_3634_ = v_a_3623_;
v_isShared_3635_ = v_isSharedCheck_3653_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_recursorMap_3632_);
lean_inc(v_visitedConstants_3629_);
lean_inc(v_visitedExprs_3628_);
lean_inc(v_visitedLevels_3627_);
lean_inc(v_visitedNames_3626_);
lean_dec(v_a_3623_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3653_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_visitedNames_3626_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_visitedLevels_3627_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_visitedExprs_3628_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_visitedConstants_3629_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3652_, 5, v_recursorMap_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*6, v_exportMData_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*6 + 1, v_exportUnsafe_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*6 + 2, v_ignoreMissing_3631_);
v___x_3638_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; 
v___x_3639_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3621_, v_a_3622_, v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v_fst_3641_; lean_object* v_snd_3642_; lean_object* v___x_3643_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v_fst_3641_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_fst_3641_);
v_snd_3642_ = lean_ctor_get(v_a_3640_, 1);
lean_inc(v_snd_3642_);
lean_dec(v_a_3640_);
v___x_3643_ = l_LeanExport_dumpExprAux(v_fst_3641_, v_a_3622_, v_snd_3642_);
return v___x_3643_;
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3639_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3639_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
}
else
{
lean_object* v___x_3655_; 
v___x_3655_ = l_LeanExport_dumpExprAux(v_e_3621_, v_a_3622_, v_a_3623_);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_3665_, size_t v_i_3666_, lean_object* v_bs_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v___x_3671_; 
v___x_3671_ = lean_usize_dec_lt(v_i_3666_, v_sz_3665_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3672_, 0, v_bs_3667_);
lean_ctor_set(v___x_3672_, 1, v___y_3669_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
return v___x_3673_;
}
else
{
lean_object* v_v_3674_; lean_object* v_toConstantVal_3675_; lean_object* v_numParams_3676_; lean_object* v_numIndices_3677_; lean_object* v_all_3678_; lean_object* v_ctors_3679_; lean_object* v_numNested_3680_; uint8_t v_isRec_3681_; uint8_t v_isUnsafe_3682_; uint8_t v_isReflexive_3683_; lean_object* v_name_3684_; lean_object* v_levelParams_3685_; lean_object* v_type_3686_; lean_object* v___x_3687_; 
v_v_3674_ = lean_array_uget_borrowed(v_bs_3667_, v_i_3666_);
v_toConstantVal_3675_ = lean_ctor_get(v_v_3674_, 0);
v_numParams_3676_ = lean_ctor_get(v_v_3674_, 1);
lean_inc(v_numParams_3676_);
v_numIndices_3677_ = lean_ctor_get(v_v_3674_, 2);
lean_inc(v_numIndices_3677_);
v_all_3678_ = lean_ctor_get(v_v_3674_, 3);
lean_inc(v_all_3678_);
v_ctors_3679_ = lean_ctor_get(v_v_3674_, 4);
lean_inc(v_ctors_3679_);
v_numNested_3680_ = lean_ctor_get(v_v_3674_, 5);
lean_inc(v_numNested_3680_);
v_isRec_3681_ = lean_ctor_get_uint8(v_v_3674_, sizeof(void*)*6);
v_isUnsafe_3682_ = lean_ctor_get_uint8(v_v_3674_, sizeof(void*)*6 + 1);
v_isReflexive_3683_ = lean_ctor_get_uint8(v_v_3674_, sizeof(void*)*6 + 2);
v_name_3684_ = lean_ctor_get(v_toConstantVal_3675_, 0);
v_levelParams_3685_ = lean_ctor_get(v_toConstantVal_3675_, 1);
lean_inc(v_levelParams_3685_);
v_type_3686_ = lean_ctor_get(v_toConstantVal_3675_, 2);
lean_inc_ref(v_type_3686_);
lean_inc(v_name_3684_);
v___x_3687_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3684_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v_fst_3689_; lean_object* v_snd_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3832_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v_fst_3689_ = lean_ctor_get(v_a_3688_, 0);
v_snd_3690_ = lean_ctor_get(v_a_3688_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3688_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3692_ = v_a_3688_;
v_isShared_3693_ = v_isSharedCheck_3832_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_snd_3690_);
lean_inc(v_fst_3689_);
lean_dec(v_a_3688_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3832_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v_bs_x27_3695_; lean_object* v_fst_3697_; lean_object* v_snd_3698_; lean_object* v___y_3704_; lean_object* v___x_3716_; 
v___x_3694_ = lean_unsigned_to_nat(0u);
v_bs_x27_3695_ = lean_array_uset(v_bs_3667_, v_i_3666_, v___x_3694_);
v___x_3716_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3685_, v___y_3668_, v_snd_3690_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3831_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3831_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3831_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v_fst_3721_; lean_object* v_snd_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3830_; 
v_fst_3721_ = lean_ctor_get(v_a_3717_, 0);
v_snd_3722_ = lean_ctor_get(v_a_3717_, 1);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_a_3717_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3724_ = v_a_3717_;
v_isShared_3725_ = v_isSharedCheck_3830_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_snd_3722_);
lean_inc(v_fst_3721_);
lean_dec(v_a_3717_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3830_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_LeanExport_dumpExpr(v_type_3686_, v___y_3668_, v_snd_3722_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v_fst_3728_; lean_object* v_snd_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3821_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v_fst_3728_ = lean_ctor_get(v_a_3727_, 0);
v_snd_3729_ = lean_ctor_get(v_a_3727_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3731_ = v_a_3727_;
v_isShared_3732_ = v_isSharedCheck_3821_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_snd_3729_);
lean_inc(v_fst_3728_);
lean_dec(v_a_3727_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3821_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3678_, v___y_3668_, v_snd_3729_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3820_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3820_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3820_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_fst_3738_; lean_object* v_snd_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3819_; 
v_fst_3738_ = lean_ctor_get(v_a_3734_, 0);
v_snd_3739_ = lean_ctor_get(v_a_3734_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_a_3734_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3741_ = v_a_3734_;
v_isShared_3742_ = v_isSharedCheck_3819_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_snd_3739_);
lean_inc(v_fst_3738_);
lean_dec(v_a_3734_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3819_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; 
v___x_3743_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3679_, v___y_3668_, v_snd_3739_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3818_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3818_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3818_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3817_; 
v_fst_3748_ = lean_ctor_get(v_a_3744_, 0);
v_snd_3749_ = lean_ctor_get(v_a_3744_, 1);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3751_ = v_a_3744_;
v_isShared_3752_ = v_isSharedCheck_3817_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_snd_3749_);
lean_inc(v_fst_3748_);
lean_dec(v_a_3744_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3817_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3754_ = l_Lean_JsonNumber_fromNat(v_fst_3689_);
if (v_isShared_3747_ == 0)
{
lean_ctor_set_tag(v___x_3746_, 2);
lean_ctor_set(v___x_3746_, 0, v___x_3754_);
v___x_3756_ = v___x_3746_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v___x_3756_);
lean_ctor_set(v___x_3751_, 0, v___x_3753_);
v___x_3758_ = v___x_3751_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
v___x_3759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 1, v_fst_3721_);
lean_ctor_set(v___x_3741_, 0, v___x_3759_);
v___x_3761_ = v___x_3741_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_fst_3721_);
v___x_3761_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v___x_3762_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3763_ = l_Lean_JsonNumber_fromNat(v_fst_3728_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 2);
lean_ctor_set(v___x_3736_, 0, v___x_3763_);
v___x_3765_ = v___x_3736_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3767_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 1, v___x_3765_);
lean_ctor_set(v___x_3731_, 0, v___x_3762_);
v___x_3767_ = v___x_3731_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3762_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_3769_ = l_Lean_JsonNumber_fromNat(v_numParams_3676_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 2);
lean_ctor_set(v___x_3719_, 0, v___x_3769_);
v___x_3771_ = v___x_3719_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 1, v___x_3771_);
lean_ctor_set(v___x_3724_, 0, v___x_3768_);
v___x_3773_ = v___x_3724_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_3775_ = l_Lean_JsonNumber_fromNat(v_numIndices_3677_);
v___x_3776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 1, v___x_3776_);
lean_ctor_set(v___x_3692_, 0, v___x_3774_);
v___x_3778_ = v___x_3692_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v_fst_3738_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
lean_ctor_set(v___x_3782_, 1, v_fst_3748_);
v___x_3783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_3784_ = l_Lean_JsonNumber_fromNat(v_numNested_3680_);
v___x_3785_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3783_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__4));
v___x_3788_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3788_, 0, v_isRec_3681_);
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__5));
v___x_3791_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3791_, 0, v_isReflexive_3683_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_3794_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3794_, 0, v_isUnsafe_3682_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_box(0);
v___x_3797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3792_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3789_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3786_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3782_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3780_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3778_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3773_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3767_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3761_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3758_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = l_Lean_Json_mkObj(v___x_3807_);
lean_dec_ref_known(v___x_3807_, 2);
v_fst_3697_ = v___x_3808_;
v_snd_3698_ = v_snd_3749_;
goto v___jp_3696_;
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
lean_del_object(v___x_3741_);
lean_dec(v_fst_3738_);
lean_del_object(v___x_3736_);
lean_del_object(v___x_3731_);
lean_dec(v_fst_3728_);
lean_del_object(v___x_3724_);
lean_dec(v_fst_3721_);
lean_del_object(v___x_3719_);
lean_del_object(v___x_3692_);
lean_dec(v_fst_3689_);
lean_dec(v_numNested_3680_);
lean_dec(v_numIndices_3677_);
lean_dec(v_numParams_3676_);
v___y_3704_ = v___x_3743_;
goto v___jp_3703_;
}
}
}
}
else
{
lean_del_object(v___x_3731_);
lean_dec(v_fst_3728_);
lean_del_object(v___x_3724_);
lean_dec(v_fst_3721_);
lean_del_object(v___x_3719_);
lean_del_object(v___x_3692_);
lean_dec(v_fst_3689_);
lean_dec(v_numNested_3680_);
lean_dec(v_ctors_3679_);
lean_dec(v_numIndices_3677_);
lean_dec(v_numParams_3676_);
v___y_3704_ = v___x_3733_;
goto v___jp_3703_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_del_object(v___x_3724_);
lean_dec(v_fst_3721_);
lean_del_object(v___x_3719_);
lean_dec_ref(v_bs_x27_3695_);
lean_del_object(v___x_3692_);
lean_dec(v_fst_3689_);
lean_dec(v_numNested_3680_);
lean_dec(v_ctors_3679_);
lean_dec(v_all_3678_);
lean_dec(v_numIndices_3677_);
lean_dec(v_numParams_3676_);
v_a_3822_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3726_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3726_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3692_);
lean_dec(v_fst_3689_);
lean_dec_ref(v_type_3686_);
lean_dec(v_numNested_3680_);
lean_dec(v_ctors_3679_);
lean_dec(v_all_3678_);
lean_dec(v_numIndices_3677_);
lean_dec(v_numParams_3676_);
v___y_3704_ = v___x_3716_;
goto v___jp_3703_;
}
v___jp_3696_:
{
size_t v___x_3699_; size_t v___x_3700_; lean_object* v___x_3701_; 
v___x_3699_ = ((size_t)1ULL);
v___x_3700_ = lean_usize_add(v_i_3666_, v___x_3699_);
v___x_3701_ = lean_array_uset(v_bs_x27_3695_, v_i_3666_, v_fst_3697_);
v_i_3666_ = v___x_3700_;
v_bs_3667_ = v___x_3701_;
v___y_3669_ = v_snd_3698_;
goto _start;
}
v___jp_3703_:
{
if (lean_obj_tag(v___y_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v_fst_3706_; lean_object* v_snd_3707_; 
v_a_3705_ = lean_ctor_get(v___y_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___y_3704_, 1);
v_fst_3706_ = lean_ctor_get(v_a_3705_, 0);
lean_inc(v_fst_3706_);
v_snd_3707_ = lean_ctor_get(v_a_3705_, 1);
lean_inc(v_snd_3707_);
lean_dec(v_a_3705_);
v_fst_3697_ = v_fst_3706_;
v_snd_3698_ = v_snd_3707_;
goto v___jp_3696_;
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v_bs_x27_3695_);
v_a_3708_ = lean_ctor_get(v___y_3704_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___y_3704_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___y_3704_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___y_3704_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v_type_3686_);
lean_dec(v_levelParams_3685_);
lean_dec(v_numNested_3680_);
lean_dec(v_ctors_3679_);
lean_dec(v_all_3678_);
lean_dec(v_numIndices_3677_);
lean_dec(v_numParams_3676_);
lean_dec_ref(v_bs_3667_);
v_a_3833_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3687_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3687_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(size_t v_sz_3844_, size_t v_i_3845_, lean_object* v_bs_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = lean_usize_dec_lt(v_i_3845_, v_sz_3844_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v_bs_3846_);
lean_ctor_set(v___x_3851_, 1, v___y_3848_);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
else
{
lean_object* v_v_3853_; lean_object* v_toConstantVal_3854_; lean_object* v_induct_3855_; lean_object* v_cidx_3856_; lean_object* v_numParams_3857_; lean_object* v_numFields_3858_; uint8_t v_isUnsafe_3859_; lean_object* v_name_3860_; lean_object* v_levelParams_3861_; lean_object* v_type_3862_; lean_object* v___x_3863_; 
v_v_3853_ = lean_array_uget_borrowed(v_bs_3846_, v_i_3845_);
v_toConstantVal_3854_ = lean_ctor_get(v_v_3853_, 0);
v_induct_3855_ = lean_ctor_get(v_v_3853_, 1);
lean_inc(v_induct_3855_);
v_cidx_3856_ = lean_ctor_get(v_v_3853_, 2);
lean_inc(v_cidx_3856_);
v_numParams_3857_ = lean_ctor_get(v_v_3853_, 3);
lean_inc(v_numParams_3857_);
v_numFields_3858_ = lean_ctor_get(v_v_3853_, 4);
lean_inc(v_numFields_3858_);
v_isUnsafe_3859_ = lean_ctor_get_uint8(v_v_3853_, sizeof(void*)*5);
v_name_3860_ = lean_ctor_get(v_toConstantVal_3854_, 0);
v_levelParams_3861_ = lean_ctor_get(v_toConstantVal_3854_, 1);
lean_inc(v_levelParams_3861_);
v_type_3862_ = lean_ctor_get(v_toConstantVal_3854_, 2);
lean_inc_ref(v_type_3862_);
lean_inc(v_name_3860_);
v___x_3863_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3860_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3977_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v_fst_3865_ = lean_ctor_get(v_a_3864_, 0);
v_snd_3866_ = lean_ctor_get(v_a_3864_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_a_3864_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3868_ = v_a_3864_;
v_isShared_3869_ = v_isSharedCheck_3977_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_snd_3866_);
lean_inc(v_fst_3865_);
lean_dec(v_a_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3977_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v_bs_x27_3871_; lean_object* v_fst_3873_; lean_object* v_snd_3874_; lean_object* v___x_3879_; 
v___x_3870_ = lean_unsigned_to_nat(0u);
v_bs_x27_3871_ = lean_array_uset(v_bs_3846_, v_i_3845_, v___x_3870_);
v___x_3879_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3861_, v___y_3847_, v_snd_3866_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_fst_3881_; lean_object* v_snd_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3965_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v_fst_3881_ = lean_ctor_get(v_a_3880_, 0);
v_snd_3882_ = lean_ctor_get(v_a_3880_, 1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_a_3880_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3884_ = v_a_3880_;
v_isShared_3885_ = v_isSharedCheck_3965_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_snd_3882_);
lean_inc(v_fst_3881_);
lean_dec(v_a_3880_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3965_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_LeanExport_dumpExpr(v_type_3862_, v___y_3847_, v_snd_3882_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v_fst_3888_; lean_object* v_snd_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3956_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v_fst_3888_ = lean_ctor_get(v_a_3887_, 0);
v_snd_3889_ = lean_ctor_get(v_a_3887_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_a_3887_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3891_ = v_a_3887_;
v_isShared_3892_ = v_isSharedCheck_3956_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_snd_3889_);
lean_inc(v_fst_3888_);
lean_dec(v_a_3887_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3956_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; 
v___x_3893_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_3855_, v___y_3847_, v_snd_3889_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v_fst_3895_; lean_object* v_snd_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3947_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v_fst_3895_ = lean_ctor_get(v_a_3894_, 0);
v_snd_3896_ = lean_ctor_get(v_a_3894_, 1);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_a_3894_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3898_ = v_a_3894_;
v_isShared_3899_ = v_isSharedCheck_3947_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_snd_3896_);
lean_inc(v_fst_3895_);
lean_dec(v_a_3894_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3947_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3904_; 
v___x_3900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_3901_ = l_Lean_JsonNumber_fromNat(v_fst_3865_);
v___x_3902_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 1, v___x_3902_);
lean_ctor_set(v___x_3898_, 0, v___x_3900_);
v___x_3904_ = v___x_3898_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 1, v_fst_3881_);
lean_ctor_set(v___x_3891_, 0, v___x_3905_);
v___x_3907_ = v___x_3891_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_fst_3881_);
v___x_3907_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3908_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3909_ = l_Lean_JsonNumber_fromNat(v_fst_3888_);
v___x_3910_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 1, v___x_3910_);
lean_ctor_set(v___x_3884_, 0, v___x_3908_);
v___x_3912_ = v___x_3884_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__2));
v___x_3914_ = l_Lean_JsonNumber_fromNat(v_fst_3895_);
v___x_3915_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3915_);
lean_ctor_set(v___x_3868_, 0, v___x_3913_);
v___x_3917_ = v___x_3868_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__3));
v___x_3919_ = l_Lean_JsonNumber_fromNat(v_cidx_3856_);
v___x_3920_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3918_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_3923_ = l_Lean_JsonNumber_fromNat(v_numParams_3857_);
v___x_3924_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3922_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__5));
v___x_3927_ = l_Lean_JsonNumber_fromNat(v_numFields_3858_);
v___x_3928_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3926_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_3931_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3931_, 0, v_isUnsafe_3859_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = lean_box(0);
v___x_3934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3929_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3925_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3921_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3917_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3912_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3907_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3904_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = l_Lean_Json_mkObj(v___x_3941_);
lean_dec_ref_known(v___x_3941_, 2);
v_fst_3873_ = v___x_3942_;
v_snd_3874_ = v_snd_3896_;
goto v___jp_3872_;
}
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_del_object(v___x_3891_);
lean_dec(v_fst_3888_);
lean_del_object(v___x_3884_);
lean_dec(v_fst_3881_);
lean_dec_ref(v_bs_x27_3871_);
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec(v_numFields_3858_);
lean_dec(v_numParams_3857_);
lean_dec(v_cidx_3856_);
v_a_3948_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3893_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3893_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_del_object(v___x_3884_);
lean_dec(v_fst_3881_);
lean_dec_ref(v_bs_x27_3871_);
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec(v_numFields_3858_);
lean_dec(v_numParams_3857_);
lean_dec(v_cidx_3856_);
lean_dec(v_induct_3855_);
v_a_3957_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3886_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3886_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
else
{
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec_ref(v_type_3862_);
lean_dec(v_numFields_3858_);
lean_dec(v_numParams_3857_);
lean_dec(v_cidx_3856_);
lean_dec(v_induct_3855_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; 
v_a_3966_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3879_, 1);
v_fst_3967_ = lean_ctor_get(v_a_3966_, 0);
lean_inc(v_fst_3967_);
v_snd_3968_ = lean_ctor_get(v_a_3966_, 1);
lean_inc(v_snd_3968_);
lean_dec(v_a_3966_);
v_fst_3873_ = v_fst_3967_;
v_snd_3874_ = v_snd_3968_;
goto v___jp_3872_;
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec_ref(v_bs_x27_3871_);
v_a_3969_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3879_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3879_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
v___jp_3872_:
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = ((size_t)1ULL);
v___x_3876_ = lean_usize_add(v_i_3845_, v___x_3875_);
v___x_3877_ = lean_array_uset(v_bs_x27_3871_, v_i_3845_, v_fst_3873_);
v_i_3845_ = v___x_3876_;
v_bs_3846_ = v___x_3877_;
v___y_3848_ = v_snd_3874_;
goto _start;
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec_ref(v_type_3862_);
lean_dec(v_levelParams_3861_);
lean_dec(v_numFields_3858_);
lean_dec(v_numParams_3857_);
lean_dec(v_cidx_3856_);
lean_dec(v_induct_3855_);
lean_dec_ref(v_bs_3846_);
v_a_3978_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3863_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3863_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v_ctor_3992_; lean_object* v_nfields_3993_; lean_object* v_rhs_3994_; lean_object* v___x_3995_; 
v_ctor_3992_ = lean_ctor_get(v_rule_3988_, 0);
lean_inc(v_ctor_3992_);
v_nfields_3993_ = lean_ctor_get(v_rule_3988_, 1);
lean_inc(v_nfields_3993_);
v_rhs_3994_ = lean_ctor_get(v_rule_3988_, 2);
lean_inc_ref(v_rhs_3994_);
lean_dec_ref(v_rule_3988_);
v___x_3995_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_3992_, v_a_3989_, v_a_3990_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v_fst_3997_; lean_object* v_snd_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4047_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
v_fst_3997_ = lean_ctor_get(v_a_3996_, 0);
v_snd_3998_ = lean_ctor_get(v_a_3996_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_a_3996_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4000_ = v_a_3996_;
v_isShared_4001_ = v_isSharedCheck_4047_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_snd_3998_);
lean_inc(v_fst_3997_);
lean_dec(v_a_3996_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4047_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_LeanExport_dumpExpr(v_rhs_3994_, v_a_3989_, v_snd_3998_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4038_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4005_ = v___x_4002_;
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_4002_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v_fst_4007_; lean_object* v_snd_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4037_; 
v_fst_4007_ = lean_ctor_get(v_a_4003_, 0);
v_snd_4008_ = lean_ctor_get(v_a_4003_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v_a_4003_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4010_ = v_a_4003_;
v_isShared_4011_ = v_isSharedCheck_4037_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_snd_4008_);
lean_inc(v_fst_4007_);
lean_dec(v_a_4003_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4037_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4016_; 
v___x_4012_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_4013_ = l_Lean_JsonNumber_fromNat(v_fst_3997_);
v___x_4014_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 1, v___x_4014_);
lean_ctor_set(v___x_4010_, 0, v___x_4012_);
v___x_4016_ = v___x_4010_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4017_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_4018_ = l_Lean_JsonNumber_fromNat(v_nfields_3993_);
v___x_4019_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 1, v___x_4019_);
lean_ctor_set(v___x_4000_, 0, v___x_4017_);
v___x_4021_ = v___x_4000_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4022_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_4023_ = l_Lean_JsonNumber_fromNat(v_fst_4007_);
v___x_4024_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4022_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
v___x_4026_ = lean_box(0);
v___x_4027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4021_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4016_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l_Lean_Json_mkObj(v___x_4029_);
lean_dec_ref_known(v___x_4029_, 2);
v___x_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v_snd_4008_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4031_);
v___x_4033_ = v___x_4005_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_del_object(v___x_4000_);
lean_dec(v_fst_3997_);
lean_dec(v_nfields_3993_);
v_a_4039_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4002_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4002_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec_ref(v_rhs_3994_);
lean_dec(v_nfields_3993_);
v_a_4048_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_3995_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_3995_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4056_, lean_object* v_x_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
if (lean_obj_tag(v_x_4056_) == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = l_List_reverse___redArg(v_x_4057_);
v___x_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___y_4059_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
return v___x_4063_;
}
else
{
lean_object* v_head_4064_; lean_object* v_tail_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4085_; 
v_head_4064_ = lean_ctor_get(v_x_4056_, 0);
v_tail_4065_ = lean_ctor_get(v_x_4056_, 1);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_x_4056_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4067_ = v_x_4056_;
v_isShared_4068_ = v_isSharedCheck_4085_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_tail_4065_);
lean_inc(v_head_4064_);
lean_dec(v_x_4056_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4085_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; 
v___x_4069_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4064_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___x_4074_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v_fst_4071_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_fst_4071_);
v_snd_4072_ = lean_ctor_get(v_a_4070_, 1);
lean_inc(v_snd_4072_);
lean_dec(v_a_4070_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 1, v_x_4057_);
lean_ctor_set(v___x_4067_, 0, v_fst_4071_);
v___x_4074_ = v___x_4067_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4071_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_x_4057_);
v___x_4074_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v_x_4056_ = v_tail_4065_;
v_x_4057_ = v___x_4074_;
v___y_4059_ = v_snd_4072_;
goto _start;
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_del_object(v___x_4067_);
lean_dec(v_tail_4065_);
lean_dec(v_x_4057_);
v_a_4077_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4069_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4069_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(size_t v_sz_4090_, size_t v_i_4091_, lean_object* v_bs_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v___x_4096_; 
v___x_4096_ = lean_usize_dec_lt(v_i_4091_, v_sz_4090_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4097_, 0, v_bs_4092_);
lean_ctor_set(v___x_4097_, 1, v___y_4094_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
else
{
lean_object* v_v_4099_; lean_object* v_toConstantVal_4100_; lean_object* v_all_4101_; lean_object* v_numParams_4102_; lean_object* v_numIndices_4103_; lean_object* v_numMotives_4104_; lean_object* v_numMinors_4105_; lean_object* v_rules_4106_; uint8_t v_k_4107_; uint8_t v_isUnsafe_4108_; lean_object* v_name_4109_; lean_object* v_levelParams_4110_; lean_object* v_type_4111_; lean_object* v___x_4112_; 
v_v_4099_ = lean_array_uget_borrowed(v_bs_4092_, v_i_4091_);
v_toConstantVal_4100_ = lean_ctor_get(v_v_4099_, 0);
v_all_4101_ = lean_ctor_get(v_v_4099_, 1);
lean_inc(v_all_4101_);
v_numParams_4102_ = lean_ctor_get(v_v_4099_, 2);
lean_inc(v_numParams_4102_);
v_numIndices_4103_ = lean_ctor_get(v_v_4099_, 3);
lean_inc(v_numIndices_4103_);
v_numMotives_4104_ = lean_ctor_get(v_v_4099_, 4);
lean_inc(v_numMotives_4104_);
v_numMinors_4105_ = lean_ctor_get(v_v_4099_, 5);
lean_inc(v_numMinors_4105_);
v_rules_4106_ = lean_ctor_get(v_v_4099_, 6);
lean_inc(v_rules_4106_);
v_k_4107_ = lean_ctor_get_uint8(v_v_4099_, sizeof(void*)*7);
v_isUnsafe_4108_ = lean_ctor_get_uint8(v_v_4099_, sizeof(void*)*7 + 1);
v_name_4109_ = lean_ctor_get(v_toConstantVal_4100_, 0);
v_levelParams_4110_ = lean_ctor_get(v_toConstantVal_4100_, 1);
lean_inc(v_levelParams_4110_);
v_type_4111_ = lean_ctor_get(v_toConstantVal_4100_, 2);
lean_inc_ref(v_type_4111_);
lean_inc(v_name_4109_);
v___x_4112_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4109_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_fst_4114_; lean_object* v_snd_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4261_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v_fst_4114_ = lean_ctor_get(v_a_4113_, 0);
v_snd_4115_ = lean_ctor_get(v_a_4113_, 1);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_a_4113_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4117_ = v_a_4113_;
v_isShared_4118_ = v_isSharedCheck_4261_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_snd_4115_);
lean_inc(v_fst_4114_);
lean_dec(v_a_4113_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4261_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; lean_object* v_bs_x27_4120_; lean_object* v_fst_4122_; lean_object* v_snd_4123_; lean_object* v___y_4129_; lean_object* v___x_4141_; 
v___x_4119_ = lean_unsigned_to_nat(0u);
v_bs_x27_4120_ = lean_array_uset(v_bs_4092_, v_i_4091_, v___x_4119_);
v___x_4141_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4110_, v___y_4093_, v_snd_4115_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4260_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4260_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4260_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v_fst_4146_; lean_object* v_snd_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4259_; 
v_fst_4146_ = lean_ctor_get(v_a_4142_, 0);
v_snd_4147_ = lean_ctor_get(v_a_4142_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_a_4142_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4149_ = v_a_4142_;
v_isShared_4150_ = v_isSharedCheck_4259_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_snd_4147_);
lean_inc(v_fst_4146_);
lean_dec(v_a_4142_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4259_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_LeanExport_dumpExpr(v_type_4111_, v___y_4093_, v_snd_4147_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v_fst_4153_; lean_object* v_snd_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4250_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v_fst_4153_ = lean_ctor_get(v_a_4152_, 0);
v_snd_4154_ = lean_ctor_get(v_a_4152_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_a_4152_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4156_ = v_a_4152_;
v_isShared_4157_ = v_isSharedCheck_4250_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_snd_4154_);
lean_inc(v_fst_4153_);
lean_dec(v_a_4152_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4250_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4101_, v___y_4093_, v_snd_4154_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4249_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4249_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4249_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_fst_4163_; lean_object* v_snd_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4248_; 
v_fst_4163_ = lean_ctor_get(v_a_4159_, 0);
v_snd_4164_ = lean_ctor_get(v_a_4159_, 1);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_a_4159_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4166_ = v_a_4159_;
v_isShared_4167_ = v_isSharedCheck_4248_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_snd_4164_);
lean_inc(v_fst_4163_);
lean_dec(v_a_4159_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4248_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = lean_box(0);
v___x_4169_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4106_, v___x_4168_, v___y_4093_, v_snd_4164_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v_fst_4171_; lean_object* v_snd_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4239_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4169_, 1);
v_fst_4171_ = lean_ctor_get(v_a_4170_, 0);
v_snd_4172_ = lean_ctor_get(v_a_4170_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_a_4170_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4174_ = v_a_4170_;
v_isShared_4175_ = v_isSharedCheck_4239_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_snd_4172_);
lean_inc(v_fst_4171_);
lean_dec(v_a_4170_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4239_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4177_ = l_Lean_JsonNumber_fromNat(v_fst_4114_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set_tag(v___x_4161_, 2);
lean_ctor_set(v___x_4161_, 0, v___x_4177_);
v___x_4179_ = v___x_4161_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4181_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v___x_4179_);
lean_ctor_set(v___x_4174_, 0, v___x_4176_);
v___x_4181_ = v___x_4174_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 1, v_fst_4146_);
lean_ctor_set(v___x_4166_, 0, v___x_4182_);
v___x_4184_ = v___x_4166_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4182_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_fst_4146_);
v___x_4184_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
v___x_4185_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4186_ = l_Lean_JsonNumber_fromNat(v_fst_4153_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set_tag(v___x_4144_, 2);
lean_ctor_set(v___x_4144_, 0, v___x_4186_);
v___x_4188_ = v___x_4144_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4190_; 
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 1, v___x_4188_);
lean_ctor_set(v___x_4156_, 0, v___x_4185_);
v___x_4190_ = v___x_4156_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 1, v_fst_4163_);
lean_ctor_set(v___x_4149_, 0, v___x_4191_);
v___x_4193_ = v___x_4149_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4233_, 1, v_fst_4163_);
v___x_4193_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__4));
v___x_4195_ = l_Lean_JsonNumber_fromNat(v_numParams_4102_);
v___x_4196_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 1, v___x_4196_);
lean_ctor_set(v___x_4117_, 0, v___x_4194_);
v___x_4198_ = v___x_4117_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4200_ = l_Lean_JsonNumber_fromNat(v_numIndices_4103_);
v___x_4201_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4199_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__0));
v___x_4204_ = l_Lean_JsonNumber_fromNat(v_numMotives_4104_);
v___x_4205_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4203_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__1));
v___x_4208_ = l_Lean_JsonNumber_fromNat(v_numMinors_4105_);
v___x_4209_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4207_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__2));
v___x_4212_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4171_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___closed__3));
v___x_4215_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4215_, 0, v_k_4107_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_4218_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4218_, 0, v_isUnsafe_4108_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
lean_ctor_set(v___x_4220_, 1, v___x_4168_);
v___x_4221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4216_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
v___x_4222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4213_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
v___x_4223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4210_);
lean_ctor_set(v___x_4223_, 1, v___x_4222_);
v___x_4224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4206_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4202_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4198_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4193_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
v___x_4228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4190_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4184_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4181_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = l_Lean_Json_mkObj(v___x_4230_);
lean_dec_ref_known(v___x_4230_, 2);
v_fst_4122_ = v___x_4231_;
v_snd_4123_ = v_snd_4172_;
goto v___jp_4121_;
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
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_del_object(v___x_4166_);
lean_dec(v_fst_4163_);
lean_del_object(v___x_4161_);
lean_del_object(v___x_4156_);
lean_dec(v_fst_4153_);
lean_del_object(v___x_4149_);
lean_dec(v_fst_4146_);
lean_del_object(v___x_4144_);
lean_dec_ref(v_bs_x27_4120_);
lean_del_object(v___x_4117_);
lean_dec(v_fst_4114_);
lean_dec(v_numMinors_4105_);
lean_dec(v_numMotives_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_numParams_4102_);
v_a_4240_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4169_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4169_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4156_);
lean_dec(v_fst_4153_);
lean_del_object(v___x_4149_);
lean_dec(v_fst_4146_);
lean_del_object(v___x_4144_);
lean_del_object(v___x_4117_);
lean_dec(v_fst_4114_);
lean_dec(v_rules_4106_);
lean_dec(v_numMinors_4105_);
lean_dec(v_numMotives_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_numParams_4102_);
v___y_4129_ = v___x_4158_;
goto v___jp_4128_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_del_object(v___x_4149_);
lean_dec(v_fst_4146_);
lean_del_object(v___x_4144_);
lean_dec_ref(v_bs_x27_4120_);
lean_del_object(v___x_4117_);
lean_dec(v_fst_4114_);
lean_dec(v_rules_4106_);
lean_dec(v_numMinors_4105_);
lean_dec(v_numMotives_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_numParams_4102_);
lean_dec(v_all_4101_);
v_a_4251_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4151_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4151_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4117_);
lean_dec(v_fst_4114_);
lean_dec_ref(v_type_4111_);
lean_dec(v_rules_4106_);
lean_dec(v_numMinors_4105_);
lean_dec(v_numMotives_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_numParams_4102_);
lean_dec(v_all_4101_);
v___y_4129_ = v___x_4141_;
goto v___jp_4128_;
}
v___jp_4121_:
{
size_t v___x_4124_; size_t v___x_4125_; lean_object* v___x_4126_; 
v___x_4124_ = ((size_t)1ULL);
v___x_4125_ = lean_usize_add(v_i_4091_, v___x_4124_);
v___x_4126_ = lean_array_uset(v_bs_x27_4120_, v_i_4091_, v_fst_4122_);
v_i_4091_ = v___x_4125_;
v_bs_4092_ = v___x_4126_;
v___y_4094_ = v_snd_4123_;
goto _start;
}
v___jp_4128_:
{
if (lean_obj_tag(v___y_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v_fst_4131_; lean_object* v_snd_4132_; 
v_a_4130_ = lean_ctor_get(v___y_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___y_4129_, 1);
v_fst_4131_ = lean_ctor_get(v_a_4130_, 0);
lean_inc(v_fst_4131_);
v_snd_4132_ = lean_ctor_get(v_a_4130_, 1);
lean_inc(v_snd_4132_);
lean_dec(v_a_4130_);
v_fst_4122_ = v_fst_4131_;
v_snd_4123_ = v_snd_4132_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec_ref(v_bs_x27_4120_);
v_a_4133_ = lean_ctor_get(v___y_4129_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___y_4129_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___y_4129_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___y_4129_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec_ref(v_type_4111_);
lean_dec(v_levelParams_4110_);
lean_dec(v_rules_4106_);
lean_dec(v_numMinors_4105_);
lean_dec(v_numMotives_4104_);
lean_dec(v_numIndices_4103_);
lean_dec(v_numParams_4102_);
lean_dec(v_all_4101_);
lean_dec_ref(v_bs_4092_);
v_a_4262_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4112_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4112_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4318_, lean_object* v_as_x27_4319_, lean_object* v_b_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
if (lean_obj_tag(v_as_x27_4319_) == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v_b_4320_);
lean_ctor_set(v___x_4324_, 1, v___y_4322_);
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
else
{
lean_object* v_head_4326_; lean_object* v_tail_4327_; lean_object* v___x_4328_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___x_4359_; 
lean_dec_ref(v_b_4320_);
v_head_4326_ = lean_ctor_get(v_as_x27_4319_, 0);
v_tail_4327_ = lean_ctor_get(v_as_x27_4319_, 1);
v___x_4328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4326_);
lean_inc_ref(v___y_4321_);
v___x_4359_ = l_Lean_Environment_find_x3f(v___y_4321_, v_head_4326_, v___x_4318_);
if (lean_obj_tag(v___x_4359_) == 1)
{
lean_object* v_val_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4483_; 
v_val_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4483_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_val_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4483_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
if (lean_obj_tag(v_val_4360_) == 4)
{
lean_object* v_val_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4482_; 
v_val_4364_ = lean_ctor_get(v_val_4360_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_val_4360_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4366_ = v_val_4360_;
v_isShared_4367_ = v_isSharedCheck_4482_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_val_4364_);
lean_dec(v_val_4360_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4482_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v_toConstantVal_4368_; lean_object* v_visitedNames_4369_; lean_object* v_visitedLevels_4370_; lean_object* v_visitedExprs_4371_; lean_object* v_visitedConstants_4372_; lean_object* v_noMDataExprs_4373_; uint8_t v_exportMData_4374_; uint8_t v_exportUnsafe_4375_; uint8_t v_ignoreMissing_4376_; lean_object* v_recursorMap_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4481_; 
v_toConstantVal_4368_ = lean_ctor_get(v_val_4364_, 0);
lean_inc_ref(v_toConstantVal_4368_);
v_visitedNames_4369_ = lean_ctor_get(v___y_4322_, 0);
v_visitedLevels_4370_ = lean_ctor_get(v___y_4322_, 1);
v_visitedExprs_4371_ = lean_ctor_get(v___y_4322_, 2);
v_visitedConstants_4372_ = lean_ctor_get(v___y_4322_, 3);
v_noMDataExprs_4373_ = lean_ctor_get(v___y_4322_, 4);
v_exportMData_4374_ = lean_ctor_get_uint8(v___y_4322_, sizeof(void*)*6);
v_exportUnsafe_4375_ = lean_ctor_get_uint8(v___y_4322_, sizeof(void*)*6 + 1);
v_ignoreMissing_4376_ = lean_ctor_get_uint8(v___y_4322_, sizeof(void*)*6 + 2);
v_recursorMap_4377_ = lean_ctor_get(v___y_4322_, 5);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___y_4322_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4379_ = v___y_4322_;
v_isShared_4380_ = v_isSharedCheck_4481_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_recursorMap_4377_);
lean_inc(v_noMDataExprs_4373_);
lean_inc(v_visitedConstants_4372_);
lean_inc(v_visitedExprs_4371_);
lean_inc(v_visitedLevels_4370_);
lean_inc(v_visitedNames_4369_);
lean_dec(v___y_4322_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4481_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
uint8_t v_kind_4381_; lean_object* v_name_4382_; lean_object* v_levelParams_4383_; lean_object* v_type_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v_kind_4381_ = lean_ctor_get_uint8(v_val_4364_, sizeof(void*)*1);
lean_dec_ref(v_val_4364_);
v_name_4382_ = lean_ctor_get(v_toConstantVal_4368_, 0);
lean_inc(v_name_4382_);
v_levelParams_4383_ = lean_ctor_get(v_toConstantVal_4368_, 1);
lean_inc(v_levelParams_4383_);
v_type_4384_ = lean_ctor_get(v_toConstantVal_4368_, 2);
lean_inc_ref(v_type_4384_);
lean_dec_ref(v_toConstantVal_4368_);
lean_inc(v_head_4326_);
v___x_4385_ = l_Lean_NameHashSet_insert(v_visitedConstants_4372_, v_head_4326_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 3, v___x_4385_);
v___x_4387_ = v___x_4379_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_visitedNames_4369_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_visitedLevels_4370_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_visitedExprs_4371_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v___x_4385_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_noMDataExprs_4373_);
lean_ctor_set(v_reuseFailAlloc_4480_, 5, v_recursorMap_4377_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*6, v_exportMData_4374_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*6 + 1, v_exportUnsafe_4375_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*6 + 2, v_ignoreMissing_4376_);
v___x_4387_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4382_, v___y_4321_, v___x_4387_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v_fst_4390_; lean_object* v_snd_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4471_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_fst_4390_ = lean_ctor_get(v_a_4389_, 0);
v_snd_4391_ = lean_ctor_get(v_a_4389_, 1);
v_isSharedCheck_4471_ = !lean_is_exclusive(v_a_4389_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4393_ = v_a_4389_;
v_isShared_4394_ = v_isSharedCheck_4471_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_snd_4391_);
lean_inc(v_fst_4390_);
lean_dec(v_a_4389_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4471_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; 
v___x_4395_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4383_, v___y_4321_, v_snd_4391_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4462_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v_fst_4397_ = lean_ctor_get(v_a_4396_, 0);
v_snd_4398_ = lean_ctor_get(v_a_4396_, 1);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_a_4396_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4400_ = v_a_4396_;
v_isShared_4401_ = v_isSharedCheck_4462_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_a_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4462_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_LeanExport_dumpExpr(v_type_4384_, v___y_4321_, v_snd_4398_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v_fst_4404_; lean_object* v_snd_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4453_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v_fst_4404_ = lean_ctor_get(v_a_4403_, 0);
v_snd_4405_ = lean_ctor_get(v_a_4403_, 1);
v_isSharedCheck_4453_ = !lean_is_exclusive(v_a_4403_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4407_ = v_a_4403_;
v_isShared_4408_ = v_isSharedCheck_4453_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_snd_4405_);
lean_inc(v_fst_4404_);
lean_dec(v_a_4403_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4453_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4409_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4411_ = l_Lean_JsonNumber_fromNat(v_fst_4390_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 2);
lean_ctor_set(v___x_4366_, 0, v___x_4411_);
v___x_4413_ = v___x_4366_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4415_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 1, v___x_4413_);
lean_ctor_set(v___x_4407_, 0, v___x_4410_);
v___x_4415_ = v___x_4407_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
v___x_4416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v_fst_4397_);
lean_ctor_set(v___x_4400_, 0, v___x_4416_);
v___x_4418_ = v___x_4400_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_fst_4397_);
v___x_4418_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v___x_4419_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4420_ = l_Lean_JsonNumber_fromNat(v_fst_4404_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set_tag(v___x_4362_, 2);
lean_ctor_set(v___x_4362_, 0, v___x_4420_);
v___x_4422_ = v___x_4362_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4424_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 1, v___x_4422_);
lean_ctor_set(v___x_4393_, 0, v___x_4419_);
v___x_4424_ = v___x_4393_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4425_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4426_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4381_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4425_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_4428_ = lean_box(0);
v___x_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4424_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4418_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4415_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = l_Lean_Json_mkObj(v___x_4432_);
lean_dec_ref_known(v___x_4432_, 2);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4409_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___x_4428_);
v___x_4436_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4435_, v_snd_4405_);
lean_dec_ref_known(v___x_4435_, 2);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v_snd_4438_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_a_4437_);
lean_dec_ref_known(v___x_4436_, 1);
v_snd_4438_ = lean_ctor_get(v_a_4437_, 1);
lean_inc(v_snd_4438_);
lean_dec(v_a_4437_);
v_as_x27_4319_ = v_tail_4327_;
v_b_4320_ = v___x_4328_;
v___y_4322_ = v_snd_4438_;
goto _start;
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
v_a_4440_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4436_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4436_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
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
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_del_object(v___x_4400_);
lean_dec(v_fst_4397_);
lean_del_object(v___x_4393_);
lean_dec(v_fst_4390_);
lean_del_object(v___x_4366_);
lean_del_object(v___x_4362_);
v_a_4454_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4402_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4402_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_del_object(v___x_4393_);
lean_dec(v_fst_4390_);
lean_dec_ref(v_type_4384_);
lean_del_object(v___x_4366_);
lean_del_object(v___x_4362_);
v_a_4463_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4395_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4395_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref(v_type_4384_);
lean_dec(v_levelParams_4383_);
lean_del_object(v___x_4366_);
lean_del_object(v___x_4362_);
v_a_4472_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4388_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4388_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4362_);
lean_dec(v_val_4360_);
v___y_4330_ = v___y_4321_;
v___y_4331_ = v___y_4322_;
goto v___jp_4329_;
}
}
}
else
{
lean_dec(v___x_4359_);
v___y_4330_ = v___y_4321_;
v___y_4331_ = v___y_4322_;
goto v___jp_4329_;
}
v___jp_4329_:
{
uint8_t v_ignoreMissing_4332_; 
v_ignoreMissing_4332_ = lean_ctor_get_uint8(v___y_4331_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4332_ == 0)
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4333_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4334_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4335_ = lean_unsigned_to_nat(313u);
v___x_4336_ = lean_unsigned_to_nat(52u);
v___x_4337_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4338_ = 1;
lean_inc(v_head_4326_);
v___x_4339_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4326_, v___x_4338_);
v___x_4340_ = lean_string_append(v___x_4337_, v___x_4339_);
lean_dec_ref(v___x_4339_);
v___x_4341_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4342_ = lean_string_append(v___x_4340_, v___x_4341_);
v___x_4343_ = l_mkPanicMessageWithDecl(v___x_4333_, v___x_4334_, v___x_4335_, v___x_4336_, v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4343_, v___y_4330_, v___y_4331_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v_snd_4346_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v_snd_4346_ = lean_ctor_get(v_a_4345_, 1);
lean_inc(v_snd_4346_);
lean_dec(v_a_4345_);
v_as_x27_4319_ = v_tail_4327_;
v_b_4320_ = v___x_4328_;
v___y_4322_ = v_snd_4346_;
goto _start;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4344_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4344_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
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
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
lean_ctor_set(v___x_4357_, 1, v___y_4331_);
v___x_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
return v___x_4358_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = l_Lean_NameSet_empty;
v___x_4487_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
lean_ctor_set(v___x_4488_, 1, v___x_4486_);
return v___x_4488_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4490_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
lean_ctor_set(v___x_4491_, 1, v___x_4489_);
return v___x_4491_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4494_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4495_ = lean_unsigned_to_nat(11u);
v___x_4496_ = lean_unsigned_to_nat(341u);
v___x_4497_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4498_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4499_ = l_mkPanicMessageWithDecl(v___x_4498_, v___x_4497_, v___x_4496_, v___x_4495_, v___x_4494_);
return v___x_4499_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4502_ = lean_unsigned_to_nat(6u);
v___x_4503_ = lean_unsigned_to_nat(329u);
v___x_4504_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_4505_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4506_ = l_mkPanicMessageWithDecl(v___x_4505_, v___x_4504_, v___x_4503_, v___x_4502_, v___x_4501_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4507_, lean_object* v_val_4508_, lean_object* v_as_x27_4509_, lean_object* v_b_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
if (lean_obj_tag(v_as_x27_4509_) == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v_b_4510_);
lean_ctor_set(v___x_4514_, 1, v___y_4512_);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
else
{
lean_object* v_head_4516_; lean_object* v_tail_4517_; lean_object* v___y_4519_; lean_object* v_snd_4550_; lean_object* v_fst_4551_; lean_object* v_fst_4552_; lean_object* v_snd_4553_; lean_object* v___y_4555_; uint8_t v___y_4556_; lean_object* v___y_4637_; lean_object* v___x_4644_; 
v_head_4516_ = lean_ctor_get(v_as_x27_4509_, 0);
v_tail_4517_ = lean_ctor_get(v_as_x27_4509_, 1);
v_snd_4550_ = lean_ctor_get(v_b_4510_, 1);
lean_inc(v_snd_4550_);
v_fst_4551_ = lean_ctor_get(v_b_4510_, 0);
lean_inc(v_fst_4551_);
lean_dec_ref(v_b_4510_);
v_fst_4552_ = lean_ctor_get(v_snd_4550_, 0);
lean_inc(v_fst_4552_);
v_snd_4553_ = lean_ctor_get(v_snd_4550_, 1);
lean_inc(v_snd_4553_);
lean_dec(v_snd_4550_);
lean_inc(v_head_4516_);
lean_inc_ref(v___y_4511_);
v___x_4644_ = l_Lean_Environment_find_x3f(v___y_4511_, v_head_4516_, v___x_4507_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__8);
v___x_4646_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4645_);
v___y_4637_ = v___x_4646_;
goto v___jp_4636_;
}
else
{
lean_object* v_val_4647_; 
v_val_4647_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_val_4647_);
lean_dec_ref_known(v___x_4644_, 1);
v___y_4637_ = v_val_4647_;
goto v___jp_4636_;
}
v___jp_4518_:
{
if (lean_obj_tag(v___y_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4541_; 
v_a_4520_ = lean_ctor_get(v___y_4519_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___y_4519_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4522_ = v___y_4519_;
v_isShared_4523_ = v_isSharedCheck_4541_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___y_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4541_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v_fst_4524_; 
v_fst_4524_ = lean_ctor_get(v_a_4520_, 0);
lean_inc(v_fst_4524_);
if (lean_obj_tag(v_fst_4524_) == 0)
{
lean_object* v_snd_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4536_; 
v_snd_4525_ = lean_ctor_get(v_a_4520_, 1);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_a_4520_);
if (v_isSharedCheck_4536_ == 0)
{
lean_object* v_unused_4537_; 
v_unused_4537_ = lean_ctor_get(v_a_4520_, 0);
lean_dec(v_unused_4537_);
v___x_4527_ = v_a_4520_;
v_isShared_4528_ = v_isSharedCheck_4536_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_snd_4525_);
lean_dec(v_a_4520_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4536_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_a_4529_; lean_object* v___x_4531_; 
v_a_4529_ = lean_ctor_get(v_fst_4524_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v_fst_4524_, 1);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v_a_4529_);
v___x_4531_ = v___x_4527_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_snd_4525_);
v___x_4531_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
lean_object* v___x_4533_; 
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4531_);
v___x_4533_ = v___x_4522_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
else
{
lean_object* v_snd_4538_; lean_object* v_a_4539_; 
lean_del_object(v___x_4522_);
v_snd_4538_ = lean_ctor_get(v_a_4520_, 1);
lean_inc(v_snd_4538_);
lean_dec(v_a_4520_);
v_a_4539_ = lean_ctor_get(v_fst_4524_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v_fst_4524_, 1);
v_as_x27_4509_ = v_tail_4517_;
v_b_4510_ = v_a_4539_;
v___y_4512_ = v_snd_4538_;
goto _start;
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
v_a_4542_ = lean_ctor_get(v___y_4519_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___y_4519_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___y_4519_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___y_4519_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
v___jp_4554_:
{
lean_object* v_toConstantVal_4557_; lean_object* v_ctors_4558_; lean_object* v___x_4559_; 
v_toConstantVal_4557_ = lean_ctor_get(v___y_4555_, 0);
v_ctors_4558_ = lean_ctor_get(v___y_4555_, 4);
v___x_4559_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4556_, v___x_4507_, v_ctors_4558_, v_fst_4552_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v_snd_4561_; lean_object* v_fst_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4627_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_a_4560_);
lean_dec_ref_known(v___x_4559_, 1);
v_snd_4561_ = lean_ctor_get(v_a_4560_, 1);
v_fst_4562_ = lean_ctor_get(v_a_4560_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_a_4560_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4564_ = v_a_4560_;
v_isShared_4565_ = v_isSharedCheck_4627_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_snd_4561_);
lean_inc(v_fst_4562_);
lean_dec(v_a_4560_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4627_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v_visitedNames_4566_; lean_object* v_visitedLevels_4567_; lean_object* v_visitedExprs_4568_; lean_object* v_visitedConstants_4569_; lean_object* v_noMDataExprs_4570_; uint8_t v_exportMData_4571_; uint8_t v_exportUnsafe_4572_; uint8_t v_ignoreMissing_4573_; lean_object* v_recursorMap_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4626_; 
v_visitedNames_4566_ = lean_ctor_get(v_snd_4561_, 0);
v_visitedLevels_4567_ = lean_ctor_get(v_snd_4561_, 1);
v_visitedExprs_4568_ = lean_ctor_get(v_snd_4561_, 2);
v_visitedConstants_4569_ = lean_ctor_get(v_snd_4561_, 3);
v_noMDataExprs_4570_ = lean_ctor_get(v_snd_4561_, 4);
v_exportMData_4571_ = lean_ctor_get_uint8(v_snd_4561_, sizeof(void*)*6);
v_exportUnsafe_4572_ = lean_ctor_get_uint8(v_snd_4561_, sizeof(void*)*6 + 1);
v_ignoreMissing_4573_ = lean_ctor_get_uint8(v_snd_4561_, sizeof(void*)*6 + 2);
v_recursorMap_4574_ = lean_ctor_get(v_snd_4561_, 5);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_snd_4561_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4576_ = v_snd_4561_;
v_isShared_4577_ = v_isSharedCheck_4626_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_recursorMap_4574_);
lean_inc(v_noMDataExprs_4570_);
lean_inc(v_visitedConstants_4569_);
lean_inc(v_visitedExprs_4568_);
lean_inc(v_visitedLevels_4567_);
lean_inc(v_visitedNames_4566_);
lean_dec(v_snd_4561_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4626_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_type_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v_type_4578_ = lean_ctor_get(v_toConstantVal_4557_, 2);
lean_inc(v_head_4516_);
v___x_4579_ = l_Lean_NameHashSet_insert(v_visitedConstants_4569_, v_head_4516_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 3, v___x_4579_);
v___x_4581_ = v___x_4576_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_visitedNames_4566_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_visitedLevels_4567_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_visitedExprs_4568_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_noMDataExprs_4570_);
lean_ctor_set(v_reuseFailAlloc_4625_, 5, v_recursorMap_4574_);
lean_ctor_set_uint8(v_reuseFailAlloc_4625_, sizeof(void*)*6, v_exportMData_4571_);
lean_ctor_set_uint8(v_reuseFailAlloc_4625_, sizeof(void*)*6 + 1, v_exportUnsafe_4572_);
lean_ctor_set_uint8(v_reuseFailAlloc_4625_, sizeof(void*)*6 + 2, v_ignoreMissing_4573_);
v___x_4581_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; 
lean_inc_ref(v_type_4578_);
v___x_4582_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4578_, v___y_4511_, v___x_4581_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v_snd_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4615_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4582_, 1);
v_snd_4584_ = lean_ctor_get(v_a_4583_, 1);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_a_4583_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; 
v_unused_4616_ = lean_ctor_get(v_a_4583_, 0);
lean_dec(v_unused_4616_);
v___x_4586_ = v_a_4583_;
v_isShared_4587_ = v_isSharedCheck_4615_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_snd_4584_);
lean_dec(v_a_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4615_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v_toConstantVal_4588_; lean_object* v_recursorMap_4589_; lean_object* v_name_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v_toConstantVal_4588_ = lean_ctor_get(v_val_4508_, 0);
v_recursorMap_4589_ = lean_ctor_get(v_snd_4584_, 5);
v_name_4590_ = lean_ctor_get(v_toConstantVal_4588_, 0);
v___x_4591_ = lean_array_push(v_fst_4551_, v___y_4555_);
v___x_4592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4589_, v_name_4590_);
if (lean_obj_tag(v___x_4592_) == 1)
{
lean_object* v_val_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4597_; 
v_val_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_val_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v___x_4594_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4595_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4594_, v_snd_4553_, v_val_4593_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 1, v___x_4595_);
lean_ctor_set(v___x_4586_, 0, v_fst_4562_);
v___x_4597_ = v___x_4586_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_fst_4562_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4599_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 1, v___x_4597_);
lean_ctor_set(v___x_4564_, 0, v___x_4591_);
v___x_4599_ = v___x_4564_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
v_as_x27_4509_ = v_tail_4517_;
v_b_4510_ = v___x_4599_;
v___y_4512_ = v_snd_4584_;
goto _start;
}
}
}
else
{
lean_object* v___x_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
lean_dec(v___x_4592_);
v___x_4603_ = lean_array_get_size(v_fst_4562_);
v___x_4604_ = lean_unsigned_to_nat(0u);
v___x_4605_ = lean_nat_dec_eq(v___x_4603_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec_ref(v___x_4591_);
lean_del_object(v___x_4586_);
lean_del_object(v___x_4564_);
lean_dec(v_fst_4562_);
lean_dec(v_snd_4553_);
v___x_4606_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4607_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4606_, v___y_4511_, v_snd_4584_);
v___y_4519_ = v___x_4607_;
goto v___jp_4518_;
}
else
{
lean_object* v___x_4609_; 
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 1, v_snd_4553_);
lean_ctor_set(v___x_4586_, 0, v_fst_4562_);
v___x_4609_ = v___x_4586_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_fst_4562_);
lean_ctor_set(v_reuseFailAlloc_4614_, 1, v_snd_4553_);
v___x_4609_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4611_; 
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 1, v___x_4609_);
lean_ctor_set(v___x_4564_, 0, v___x_4591_);
v___x_4611_ = v___x_4564_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
v_as_x27_4509_ = v_tail_4517_;
v_b_4510_ = v___x_4611_;
v___y_4512_ = v_snd_4584_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_del_object(v___x_4564_);
lean_dec(v_fst_4562_);
lean_dec_ref(v___y_4555_);
lean_dec(v_snd_4553_);
lean_dec(v_fst_4551_);
v_a_4617_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4582_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4582_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v___y_4555_);
lean_dec(v_snd_4553_);
lean_dec(v_fst_4551_);
v_a_4628_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4559_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4559_);
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
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_4636_:
{
lean_object* v___x_4638_; uint8_t v_isUnsafe_4639_; 
v___x_4638_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4637_);
lean_dec_ref(v___y_4637_);
v_isUnsafe_4639_ = lean_ctor_get_uint8(v___x_4638_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4639_ == 0)
{
uint8_t v___x_4640_; 
v___x_4640_ = 1;
v___y_4555_ = v___x_4638_;
v___y_4556_ = v___x_4640_;
goto v___jp_4554_;
}
else
{
if (v___x_4507_ == 0)
{
uint8_t v_exportUnsafe_4641_; 
v_exportUnsafe_4641_ = lean_ctor_get_uint8(v___y_4512_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4641_ == 0)
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
lean_dec_ref(v___x_4638_);
lean_dec(v_snd_4553_);
lean_dec(v_fst_4552_);
lean_dec(v_fst_4551_);
v___x_4642_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4643_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4642_, v___y_4511_, v___y_4512_);
v___y_4519_ = v___x_4643_;
goto v___jp_4518_;
}
else
{
v___y_4555_ = v___x_4638_;
v___y_4556_ = v_exportUnsafe_4641_;
goto v___jp_4554_;
}
}
else
{
v___y_4555_ = v___x_4638_;
v___y_4556_ = v___x_4507_;
goto v___jp_4554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_4648_, size_t v_sz_4649_, size_t v_i_4650_, lean_object* v_b_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
uint8_t v___x_4655_; 
v___x_4655_ = lean_usize_dec_lt(v_i_4650_, v_sz_4649_);
if (v___x_4655_ == 0)
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v_b_4651_);
lean_ctor_set(v___x_4656_, 1, v___y_4653_);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
else
{
lean_object* v_visitedNames_4658_; lean_object* v_visitedLevels_4659_; lean_object* v_visitedExprs_4660_; lean_object* v_visitedConstants_4661_; lean_object* v_noMDataExprs_4662_; uint8_t v_exportMData_4663_; uint8_t v_exportUnsafe_4664_; uint8_t v_ignoreMissing_4665_; lean_object* v_recursorMap_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4685_; 
v_visitedNames_4658_ = lean_ctor_get(v___y_4653_, 0);
v_visitedLevels_4659_ = lean_ctor_get(v___y_4653_, 1);
v_visitedExprs_4660_ = lean_ctor_get(v___y_4653_, 2);
v_visitedConstants_4661_ = lean_ctor_get(v___y_4653_, 3);
v_noMDataExprs_4662_ = lean_ctor_get(v___y_4653_, 4);
v_exportMData_4663_ = lean_ctor_get_uint8(v___y_4653_, sizeof(void*)*6);
v_exportUnsafe_4664_ = lean_ctor_get_uint8(v___y_4653_, sizeof(void*)*6 + 1);
v_ignoreMissing_4665_ = lean_ctor_get_uint8(v___y_4653_, sizeof(void*)*6 + 2);
v_recursorMap_4666_ = lean_ctor_get(v___y_4653_, 5);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___y_4653_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4668_ = v___y_4653_;
v_isShared_4669_ = v_isSharedCheck_4685_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_recursorMap_4666_);
lean_inc(v_noMDataExprs_4662_);
lean_inc(v_visitedConstants_4661_);
lean_inc(v_visitedExprs_4660_);
lean_inc(v_visitedLevels_4659_);
lean_inc(v_visitedNames_4658_);
lean_dec(v___y_4653_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4685_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v_a_4670_; lean_object* v_toConstantVal_4671_; lean_object* v_name_4672_; lean_object* v_type_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v_a_4670_ = lean_array_uget_borrowed(v_as_4648_, v_i_4650_);
v_toConstantVal_4671_ = lean_ctor_get(v_a_4670_, 0);
v_name_4672_ = lean_ctor_get(v_toConstantVal_4671_, 0);
v_type_4673_ = lean_ctor_get(v_toConstantVal_4671_, 2);
lean_inc(v_name_4672_);
v___x_4674_ = l_Lean_NameHashSet_insert(v_visitedConstants_4661_, v_name_4672_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 3, v___x_4674_);
v___x_4676_ = v___x_4668_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_visitedNames_4658_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v_visitedLevels_4659_);
lean_ctor_set(v_reuseFailAlloc_4684_, 2, v_visitedExprs_4660_);
lean_ctor_set(v_reuseFailAlloc_4684_, 3, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4684_, 4, v_noMDataExprs_4662_);
lean_ctor_set(v_reuseFailAlloc_4684_, 5, v_recursorMap_4666_);
lean_ctor_set_uint8(v_reuseFailAlloc_4684_, sizeof(void*)*6, v_exportMData_4663_);
lean_ctor_set_uint8(v_reuseFailAlloc_4684_, sizeof(void*)*6 + 1, v_exportUnsafe_4664_);
lean_ctor_set_uint8(v_reuseFailAlloc_4684_, sizeof(void*)*6 + 2, v_ignoreMissing_4665_);
v___x_4676_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; 
lean_inc_ref(v_type_4673_);
v___x_4677_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4673_, v___y_4652_, v___x_4676_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v_snd_4679_; lean_object* v___x_4680_; size_t v___x_4681_; size_t v___x_4682_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4677_, 1);
v_snd_4679_ = lean_ctor_get(v_a_4678_, 1);
lean_inc(v_snd_4679_);
lean_dec(v_a_4678_);
v___x_4680_ = lean_box(0);
v___x_4681_ = ((size_t)1ULL);
v___x_4682_ = lean_usize_add(v_i_4650_, v___x_4681_);
v_i_4650_ = v___x_4682_;
v_b_4651_ = v___x_4680_;
v___y_4653_ = v_snd_4679_;
goto _start;
}
else
{
return v___x_4677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4686_, lean_object* v_b_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
if (lean_obj_tag(v_as_x27_4686_) == 0)
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4691_, 0, v_b_4687_);
lean_ctor_set(v___x_4691_, 1, v___y_4689_);
v___x_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
return v___x_4692_;
}
else
{
lean_object* v_head_4693_; lean_object* v_tail_4694_; lean_object* v___x_4695_; 
v_head_4693_ = lean_ctor_get(v_as_x27_4686_, 0);
v_tail_4694_ = lean_ctor_get(v_as_x27_4686_, 1);
lean_inc(v_head_4693_);
v___x_4695_ = l_LeanExport_dumpConstant(v_head_4693_, v___y_4688_, v___y_4689_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v_snd_4697_; lean_object* v___x_4698_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_snd_4697_ = lean_ctor_get(v_a_4696_, 1);
lean_inc(v_snd_4697_);
lean_dec(v_a_4696_);
v___x_4698_ = lean_box(0);
v_as_x27_4686_ = v_tail_4694_;
v_b_4687_ = v___x_4698_;
v___y_4689_ = v_snd_4697_;
goto _start;
}
else
{
return v___x_4695_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___y_4709_; lean_object* v___y_4710_; size_t v___y_4711_; lean_object* v___y_4712_; size_t v___y_4713_; lean_object* v_fst_4714_; lean_object* v_snd_4715_; uint8_t v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = 0;
lean_inc(v_c_4700_);
lean_inc_ref(v_a_4701_);
v___x_4811_ = l_Lean_Environment_find_x3f(v_a_4701_, v_c_4700_, v___x_4810_);
if (lean_obj_tag(v___x_4811_) == 1)
{
lean_object* v_val_4812_; uint8_t v___y_5551_; uint8_t v___x_5552_; 
v_val_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_val_4812_);
lean_dec_ref_known(v___x_4811_, 1);
v___x_5552_ = l_Lean_ConstantInfo_isUnsafe(v_val_4812_);
if (v___x_5552_ == 0)
{
v___y_5551_ = v___x_5552_;
goto v___jp_5550_;
}
else
{
uint8_t v_exportUnsafe_5553_; 
v_exportUnsafe_5553_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5553_ == 0)
{
v___y_5551_ = v___x_5552_;
goto v___jp_5550_;
}
else
{
goto v___jp_4813_;
}
}
v___jp_4813_:
{
lean_object* v_visitedNames_4814_; lean_object* v_visitedLevels_4815_; lean_object* v_visitedExprs_4816_; lean_object* v_visitedConstants_4817_; lean_object* v_noMDataExprs_4818_; uint8_t v_exportMData_4819_; uint8_t v_exportUnsafe_4820_; uint8_t v_ignoreMissing_4821_; lean_object* v_recursorMap_4822_; uint8_t v___x_4823_; 
v_visitedNames_4814_ = lean_ctor_get(v_a_4702_, 0);
v_visitedLevels_4815_ = lean_ctor_get(v_a_4702_, 1);
v_visitedExprs_4816_ = lean_ctor_get(v_a_4702_, 2);
v_visitedConstants_4817_ = lean_ctor_get(v_a_4702_, 3);
v_noMDataExprs_4818_ = lean_ctor_get(v_a_4702_, 4);
v_exportMData_4819_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6);
v_exportUnsafe_4820_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6 + 1);
v_ignoreMissing_4821_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6 + 2);
v_recursorMap_4822_ = lean_ctor_get(v_a_4702_, 5);
v___x_4823_ = l_Lean_NameHashSet_contains(v_visitedConstants_4817_, v_c_4700_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_5543_; 
lean_inc(v_recursorMap_4822_);
lean_inc_ref(v_noMDataExprs_4818_);
lean_inc_ref(v_visitedConstants_4817_);
lean_inc_ref(v_visitedExprs_4816_);
lean_inc_ref(v_visitedLevels_4815_);
lean_inc_ref(v_visitedNames_4814_);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_a_4702_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; lean_object* v_unused_5545_; lean_object* v_unused_5546_; lean_object* v_unused_5547_; lean_object* v_unused_5548_; lean_object* v_unused_5549_; 
v_unused_5544_ = lean_ctor_get(v_a_4702_, 5);
lean_dec(v_unused_5544_);
v_unused_5545_ = lean_ctor_get(v_a_4702_, 4);
lean_dec(v_unused_5545_);
v_unused_5546_ = lean_ctor_get(v_a_4702_, 3);
lean_dec(v_unused_5546_);
v_unused_5547_ = lean_ctor_get(v_a_4702_, 2);
lean_dec(v_unused_5547_);
v_unused_5548_ = lean_ctor_get(v_a_4702_, 1);
lean_dec(v_unused_5548_);
v_unused_5549_ = lean_ctor_get(v_a_4702_, 0);
lean_dec(v_unused_5549_);
v___x_4825_ = v_a_4702_;
v_isShared_4826_ = v_isSharedCheck_5543_;
goto v_resetjp_4824_;
}
else
{
lean_dec(v_a_4702_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_5543_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = l_Lean_NameHashSet_insert(v_visitedConstants_4817_, v_c_4700_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 3, v___x_4827_);
v___x_4829_ = v___x_4825_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_visitedNames_4814_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_visitedLevels_4815_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_visitedExprs_4816_);
lean_ctor_set(v_reuseFailAlloc_5542_, 3, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_5542_, 4, v_noMDataExprs_4818_);
lean_ctor_set(v_reuseFailAlloc_5542_, 5, v_recursorMap_4822_);
lean_ctor_set_uint8(v_reuseFailAlloc_5542_, sizeof(void*)*6, v_exportMData_4819_);
lean_ctor_set_uint8(v_reuseFailAlloc_5542_, sizeof(void*)*6 + 1, v_exportUnsafe_4820_);
lean_ctor_set_uint8(v_reuseFailAlloc_5542_, sizeof(void*)*6 + 2, v_ignoreMissing_4821_);
v___x_4829_ = v_reuseFailAlloc_5542_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
switch(lean_obj_tag(v_val_4812_))
{
case 0:
{
lean_object* v_val_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4934_; 
v_val_4830_ = lean_ctor_get(v_val_4812_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_val_4812_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4832_ = v_val_4812_;
v_isShared_4833_ = v_isSharedCheck_4934_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_val_4830_);
lean_dec(v_val_4812_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4934_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_toConstantVal_4834_; uint8_t v_isUnsafe_4835_; lean_object* v_name_4836_; lean_object* v_levelParams_4837_; lean_object* v_type_4838_; lean_object* v___x_4839_; 
v_toConstantVal_4834_ = lean_ctor_get(v_val_4830_, 0);
lean_inc_ref(v_toConstantVal_4834_);
v_isUnsafe_4835_ = lean_ctor_get_uint8(v_val_4830_, sizeof(void*)*1);
lean_dec_ref(v_val_4830_);
v_name_4836_ = lean_ctor_get(v_toConstantVal_4834_, 0);
lean_inc(v_name_4836_);
v_levelParams_4837_ = lean_ctor_get(v_toConstantVal_4834_, 1);
lean_inc(v_levelParams_4837_);
v_type_4838_ = lean_ctor_get(v_toConstantVal_4834_, 2);
lean_inc_ref_n(v_type_4838_, 2);
lean_dec_ref(v_toConstantVal_4834_);
v___x_4839_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4838_, v_a_4701_, v___x_4829_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4933_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4842_ = v___x_4839_;
v_isShared_4843_ = v_isSharedCheck_4933_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4933_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v_snd_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4931_; 
v_snd_4844_ = lean_ctor_get(v_a_4840_, 1);
v_isSharedCheck_4931_ = !lean_is_exclusive(v_a_4840_);
if (v_isSharedCheck_4931_ == 0)
{
lean_object* v_unused_4932_; 
v_unused_4932_ = lean_ctor_get(v_a_4840_, 0);
lean_dec(v_unused_4932_);
v___x_4846_ = v_a_4840_;
v_isShared_4847_ = v_isSharedCheck_4931_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_snd_4844_);
lean_dec(v_a_4840_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4931_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; 
v___x_4848_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4836_, v_a_4701_, v_snd_4844_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v_fst_4850_; lean_object* v_snd_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4922_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v_fst_4850_ = lean_ctor_get(v_a_4849_, 0);
v_snd_4851_ = lean_ctor_get(v_a_4849_, 1);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_a_4849_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4853_ = v_a_4849_;
v_isShared_4854_ = v_isSharedCheck_4922_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_snd_4851_);
lean_inc(v_fst_4850_);
lean_dec(v_a_4849_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4922_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4855_; 
v___x_4855_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4837_, v_a_4701_, v_snd_4851_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v_fst_4857_; lean_object* v_snd_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4913_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref_known(v___x_4855_, 1);
v_fst_4857_ = lean_ctor_get(v_a_4856_, 0);
v_snd_4858_ = lean_ctor_get(v_a_4856_, 1);
v_isSharedCheck_4913_ = !lean_is_exclusive(v_a_4856_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4860_ = v_a_4856_;
v_isShared_4861_ = v_isSharedCheck_4913_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_snd_4858_);
lean_inc(v_fst_4857_);
lean_dec(v_a_4856_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4913_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; 
v___x_4862_ = l_LeanExport_dumpExpr(v_type_4838_, v_a_4701_, v_snd_4858_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v_fst_4864_; lean_object* v_snd_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4904_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v_fst_4864_ = lean_ctor_get(v_a_4863_, 0);
v_snd_4865_ = lean_ctor_get(v_a_4863_, 1);
v_isSharedCheck_4904_ = !lean_is_exclusive(v_a_4863_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4867_ = v_a_4863_;
v_isShared_4868_ = v_isSharedCheck_4904_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_snd_4865_);
lean_inc(v_fst_4864_);
lean_dec(v_a_4863_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4904_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4869_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_4870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_4871_ = l_Lean_JsonNumber_fromNat(v_fst_4850_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set_tag(v___x_4842_, 2);
lean_ctor_set(v___x_4842_, 0, v___x_4871_);
v___x_4873_ = v___x_4842_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4875_; 
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 1, v___x_4873_);
lean_ctor_set(v___x_4867_, 0, v___x_4870_);
v___x_4875_ = v___x_4867_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4870_);
lean_ctor_set(v_reuseFailAlloc_4902_, 1, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 1, v_fst_4857_);
lean_ctor_set(v___x_4860_, 0, v___x_4876_);
v___x_4878_ = v___x_4860_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_fst_4857_);
v___x_4878_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4879_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4880_ = l_Lean_JsonNumber_fromNat(v_fst_4864_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set_tag(v___x_4832_, 2);
lean_ctor_set(v___x_4832_, 0, v___x_4880_);
v___x_4882_ = v___x_4832_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4884_; 
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 1, v___x_4882_);
lean_ctor_set(v___x_4853_, 0, v___x_4879_);
v___x_4884_ = v___x_4853_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4899_, 1, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_4886_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4886_, 0, v_isUnsafe_4835_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 1, v___x_4886_);
lean_ctor_set(v___x_4846_, 0, v___x_4885_);
v___x_4888_ = v___x_4846_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4889_ = lean_box(0);
v___x_4890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4888_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v___x_4891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4884_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4878_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4875_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
v___x_4894_ = l_Lean_Json_mkObj(v___x_4893_);
lean_dec_ref_known(v___x_4893_, 2);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4869_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
lean_ctor_set(v___x_4896_, 1, v___x_4889_);
v___x_4897_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4896_, v_snd_4865_);
lean_dec_ref_known(v___x_4896_, 2);
return v___x_4897_;
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
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_del_object(v___x_4860_);
lean_dec(v_fst_4857_);
lean_del_object(v___x_4853_);
lean_dec(v_fst_4850_);
lean_del_object(v___x_4846_);
lean_del_object(v___x_4842_);
lean_del_object(v___x_4832_);
v_a_4905_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4862_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4862_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
lean_del_object(v___x_4853_);
lean_dec(v_fst_4850_);
lean_del_object(v___x_4846_);
lean_del_object(v___x_4842_);
lean_dec_ref(v_type_4838_);
lean_del_object(v___x_4832_);
v_a_4914_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4855_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4855_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_del_object(v___x_4846_);
lean_del_object(v___x_4842_);
lean_dec_ref(v_type_4838_);
lean_dec(v_levelParams_4837_);
lean_del_object(v___x_4832_);
v_a_4923_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4848_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4848_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_4838_);
lean_dec(v_levelParams_4837_);
lean_dec(v_name_4836_);
lean_del_object(v___x_4832_);
return v___x_4839_;
}
}
}
case 1:
{
lean_object* v_val_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_5106_; 
v_val_4935_ = lean_ctor_get(v_val_4812_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_val_4812_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_4937_ = v_val_4812_;
v_isShared_4938_ = v_isSharedCheck_5106_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_val_4935_);
lean_dec(v_val_4812_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_5106_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v_toConstantVal_4939_; lean_object* v_value_4940_; lean_object* v_hints_4941_; uint8_t v_safety_4942_; lean_object* v_all_4943_; lean_object* v_name_4944_; lean_object* v_levelParams_4945_; lean_object* v_type_4946_; lean_object* v___x_4947_; 
v_toConstantVal_4939_ = lean_ctor_get(v_val_4935_, 0);
lean_inc_ref(v_toConstantVal_4939_);
v_value_4940_ = lean_ctor_get(v_val_4935_, 1);
lean_inc_ref(v_value_4940_);
v_hints_4941_ = lean_ctor_get(v_val_4935_, 2);
lean_inc(v_hints_4941_);
v_safety_4942_ = lean_ctor_get_uint8(v_val_4935_, sizeof(void*)*4);
v_all_4943_ = lean_ctor_get(v_val_4935_, 3);
lean_inc(v_all_4943_);
lean_dec_ref(v_val_4935_);
v_name_4944_ = lean_ctor_get(v_toConstantVal_4939_, 0);
lean_inc(v_name_4944_);
v_levelParams_4945_ = lean_ctor_get(v_toConstantVal_4939_, 1);
lean_inc(v_levelParams_4945_);
v_type_4946_ = lean_ctor_get(v_toConstantVal_4939_, 2);
lean_inc_ref_n(v_type_4946_, 2);
lean_dec_ref(v_toConstantVal_4939_);
v___x_4947_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4946_, v_a_4701_, v___x_4829_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5105_; 
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_5105_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5105_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v_snd_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_5103_; 
v_snd_4952_ = lean_ctor_get(v_a_4948_, 1);
v_isSharedCheck_5103_ = !lean_is_exclusive(v_a_4948_);
if (v_isSharedCheck_5103_ == 0)
{
lean_object* v_unused_5104_; 
v_unused_5104_ = lean_ctor_get(v_a_4948_, 0);
lean_dec(v_unused_5104_);
v___x_4954_ = v_a_4948_;
v_isShared_4955_ = v_isSharedCheck_5103_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_snd_4952_);
lean_dec(v_a_4948_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_5103_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4956_; 
lean_inc_ref(v_value_4940_);
v___x_4956_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_4940_, v_a_4701_, v_snd_4952_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_5102_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_4959_ = v___x_4956_;
v_isShared_4960_ = v_isSharedCheck_5102_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4956_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_5102_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v_snd_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_5100_; 
v_snd_4961_ = lean_ctor_get(v_a_4957_, 1);
v_isSharedCheck_5100_ = !lean_is_exclusive(v_a_4957_);
if (v_isSharedCheck_5100_ == 0)
{
lean_object* v_unused_5101_; 
v_unused_5101_ = lean_ctor_get(v_a_4957_, 0);
lean_dec(v_unused_5101_);
v___x_4963_ = v_a_4957_;
v_isShared_4964_ = v_isSharedCheck_5100_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_snd_4961_);
lean_dec(v_a_4957_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_5100_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4965_; 
v___x_4965_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4944_, v_a_4701_, v_snd_4961_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v_fst_4967_; lean_object* v_snd_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_5091_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v_fst_4967_ = lean_ctor_get(v_a_4966_, 0);
v_snd_4968_ = lean_ctor_get(v_a_4966_, 1);
v_isSharedCheck_5091_ = !lean_is_exclusive(v_a_4966_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_4970_ = v_a_4966_;
v_isShared_4971_ = v_isSharedCheck_5091_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_snd_4968_);
lean_inc(v_fst_4967_);
lean_dec(v_a_4966_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_5091_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4972_; 
v___x_4972_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4945_, v_a_4701_, v_snd_4968_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v_fst_4974_; lean_object* v_snd_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5082_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_a_4973_);
lean_dec_ref_known(v___x_4972_, 1);
v_fst_4974_ = lean_ctor_get(v_a_4973_, 0);
v_snd_4975_ = lean_ctor_get(v_a_4973_, 1);
v_isSharedCheck_5082_ = !lean_is_exclusive(v_a_4973_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_4977_ = v_a_4973_;
v_isShared_4978_ = v_isSharedCheck_5082_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_snd_4975_);
lean_inc(v_fst_4974_);
lean_dec(v_a_4973_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5082_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_LeanExport_dumpExpr(v_type_4946_, v_a_4701_, v_snd_4975_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v_fst_4981_; lean_object* v_snd_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5073_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4979_, 1);
v_fst_4981_ = lean_ctor_get(v_a_4980_, 0);
v_snd_4982_ = lean_ctor_get(v_a_4980_, 1);
v_isSharedCheck_5073_ = !lean_is_exclusive(v_a_4980_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_4984_ = v_a_4980_;
v_isShared_4985_ = v_isSharedCheck_5073_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_snd_4982_);
lean_inc(v_fst_4981_);
lean_dec(v_a_4980_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5073_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_LeanExport_dumpExpr(v_value_4940_, v_a_4701_, v_snd_4982_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v_fst_4988_; lean_object* v_snd_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5064_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v_fst_4988_ = lean_ctor_get(v_a_4987_, 0);
v_snd_4989_ = lean_ctor_get(v_a_4987_, 1);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_a_4987_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_4991_ = v_a_4987_;
v_isShared_4992_ = v_isSharedCheck_5064_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_snd_4989_);
lean_inc(v_fst_4988_);
lean_dec(v_a_4987_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5064_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4993_; 
v___x_4993_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4943_, v_a_4701_, v_snd_4989_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v_fst_4995_; lean_object* v_snd_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5055_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
v_fst_4995_ = lean_ctor_get(v_a_4994_, 0);
v_snd_4996_ = lean_ctor_get(v_a_4994_, 1);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_a_4994_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_4998_ = v_a_4994_;
v_isShared_4999_ = v_isSharedCheck_5055_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_snd_4996_);
lean_inc(v_fst_4995_);
lean_dec(v_a_4994_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5055_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_5000_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_5001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5002_ = l_Lean_JsonNumber_fromNat(v_fst_4967_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set_tag(v___x_4959_, 2);
lean_ctor_set(v___x_4959_, 0, v___x_5002_);
v___x_5004_ = v___x_4959_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5006_; 
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 1, v___x_5004_);
lean_ctor_set(v___x_4998_, 0, v___x_5001_);
v___x_5006_ = v___x_4998_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5001_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 1, v_fst_4974_);
lean_ctor_set(v___x_4991_, 0, v___x_5007_);
v___x_5009_ = v___x_4991_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5007_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_fst_4974_);
v___x_5009_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5013_; 
v___x_5010_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5011_ = l_Lean_JsonNumber_fromNat(v_fst_4981_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set_tag(v___x_4950_, 2);
lean_ctor_set(v___x_4950_, 0, v___x_5011_);
v___x_5013_ = v___x_4950_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
lean_object* v___x_5015_; 
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5013_);
lean_ctor_set(v___x_4984_, 0, v___x_5010_);
v___x_5015_ = v___x_4984_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5010_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5016_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5017_ = l_Lean_JsonNumber_fromNat(v_fst_4988_);
if (v_isShared_4938_ == 0)
{
lean_ctor_set_tag(v___x_4937_, 2);
lean_ctor_set(v___x_4937_, 0, v___x_5017_);
v___x_5019_ = v___x_4937_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5021_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 1, v___x_5019_);
lean_ctor_set(v___x_4977_, 0, v___x_5016_);
v___x_5021_ = v___x_4977_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5016_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5022_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_5023_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_4941_);
lean_dec(v_hints_4941_);
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 1, v___x_5023_);
lean_ctor_set(v___x_4970_, 0, v___x_5022_);
v___x_5025_ = v___x_4970_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
v___x_5026_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_5027_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_4942_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_5027_);
lean_ctor_set(v___x_4963_, 0, v___x_5026_);
v___x_5029_ = v___x_4963_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5026_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
lean_object* v___x_5030_; lean_object* v___x_5032_; 
v___x_5030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 1, v_fst_4995_);
lean_ctor_set(v___x_4954_, 0, v___x_5030_);
v___x_5032_ = v___x_4954_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v_fst_4995_);
v___x_5032_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5033_ = lean_box(0);
v___x_5034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5032_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
v___x_5035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5029_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
v___x_5036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5025_);
lean_ctor_set(v___x_5036_, 1, v___x_5035_);
v___x_5037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5021_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5015_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5009_);
lean_ctor_set(v___x_5039_, 1, v___x_5038_);
v___x_5040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5006_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = l_Lean_Json_mkObj(v___x_5040_);
lean_dec_ref_known(v___x_5040_, 2);
v___x_5042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5000_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
lean_ctor_set(v___x_5043_, 1, v___x_5033_);
v___x_5044_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5043_, v_snd_4996_);
lean_dec_ref_known(v___x_5043_, 2);
return v___x_5044_;
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
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_del_object(v___x_4991_);
lean_dec(v_fst_4988_);
lean_del_object(v___x_4984_);
lean_dec(v_fst_4981_);
lean_del_object(v___x_4977_);
lean_dec(v_fst_4974_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec(v_hints_4941_);
lean_del_object(v___x_4937_);
v_a_5056_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_4993_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_4993_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
lean_del_object(v___x_4984_);
lean_dec(v_fst_4981_);
lean_del_object(v___x_4977_);
lean_dec(v_fst_4974_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_del_object(v___x_4937_);
v_a_5065_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_4986_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_4986_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5081_; 
lean_del_object(v___x_4977_);
lean_dec(v_fst_4974_);
lean_del_object(v___x_4970_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_dec_ref(v_value_4940_);
lean_del_object(v___x_4937_);
v_a_5074_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_4979_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_4979_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
}
else
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_del_object(v___x_4970_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec_ref(v_type_4946_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_dec_ref(v_value_4940_);
lean_del_object(v___x_4937_);
v_a_5083_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_4972_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_4972_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
lean_del_object(v___x_4963_);
lean_del_object(v___x_4959_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec_ref(v_type_4946_);
lean_dec(v_levelParams_4945_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_dec_ref(v_value_4940_);
lean_del_object(v___x_4937_);
v_a_5092_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v___x_4965_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_4965_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_dec_ref(v_type_4946_);
lean_dec(v_levelParams_4945_);
lean_dec(v_name_4944_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_dec_ref(v_value_4940_);
lean_del_object(v___x_4937_);
return v___x_4956_;
}
}
}
}
else
{
lean_dec_ref(v_type_4946_);
lean_dec(v_levelParams_4945_);
lean_dec(v_name_4944_);
lean_dec(v_all_4943_);
lean_dec(v_hints_4941_);
lean_dec_ref(v_value_4940_);
lean_del_object(v___x_4937_);
return v___x_4947_;
}
}
}
case 2:
{
lean_object* v_val_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5268_; 
v_val_5107_ = lean_ctor_get(v_val_4812_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_val_4812_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5109_ = v_val_4812_;
v_isShared_5110_ = v_isSharedCheck_5268_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_val_5107_);
lean_dec(v_val_4812_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5268_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v_toConstantVal_5111_; lean_object* v_value_5112_; lean_object* v_all_5113_; lean_object* v_name_5114_; lean_object* v_levelParams_5115_; lean_object* v_type_5116_; lean_object* v___x_5117_; 
v_toConstantVal_5111_ = lean_ctor_get(v_val_5107_, 0);
lean_inc_ref(v_toConstantVal_5111_);
v_value_5112_ = lean_ctor_get(v_val_5107_, 1);
lean_inc_ref(v_value_5112_);
v_all_5113_ = lean_ctor_get(v_val_5107_, 2);
lean_inc(v_all_5113_);
lean_dec_ref(v_val_5107_);
v_name_5114_ = lean_ctor_get(v_toConstantVal_5111_, 0);
lean_inc(v_name_5114_);
v_levelParams_5115_ = lean_ctor_get(v_toConstantVal_5111_, 1);
lean_inc(v_levelParams_5115_);
v_type_5116_ = lean_ctor_get(v_toConstantVal_5111_, 2);
lean_inc_ref_n(v_type_5116_, 2);
lean_dec_ref(v_toConstantVal_5111_);
v___x_5117_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5116_, v_a_4701_, v___x_4829_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5267_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5120_ = v___x_5117_;
v_isShared_5121_ = v_isSharedCheck_5267_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5117_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5267_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v_snd_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5265_; 
v_snd_5122_ = lean_ctor_get(v_a_5118_, 1);
v_isSharedCheck_5265_ = !lean_is_exclusive(v_a_5118_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; 
v_unused_5266_ = lean_ctor_get(v_a_5118_, 0);
lean_dec(v_unused_5266_);
v___x_5124_ = v_a_5118_;
v_isShared_5125_ = v_isSharedCheck_5265_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_snd_5122_);
lean_dec(v_a_5118_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5265_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; 
lean_inc_ref(v_value_5112_);
v___x_5126_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5112_, v_a_4701_, v_snd_5122_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5264_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5129_ = v___x_5126_;
v_isShared_5130_ = v_isSharedCheck_5264_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5126_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5264_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v_snd_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5262_; 
v_snd_5131_ = lean_ctor_get(v_a_5127_, 1);
v_isSharedCheck_5262_ = !lean_is_exclusive(v_a_5127_);
if (v_isSharedCheck_5262_ == 0)
{
lean_object* v_unused_5263_; 
v_unused_5263_ = lean_ctor_get(v_a_5127_, 0);
lean_dec(v_unused_5263_);
v___x_5133_ = v_a_5127_;
v_isShared_5134_ = v_isSharedCheck_5262_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_snd_5131_);
lean_dec(v_a_5127_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5262_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; 
v___x_5135_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5114_, v_a_4701_, v_snd_5131_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_a_5136_; lean_object* v_fst_5137_; lean_object* v_snd_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5253_; 
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref_known(v___x_5135_, 1);
v_fst_5137_ = lean_ctor_get(v_a_5136_, 0);
v_snd_5138_ = lean_ctor_get(v_a_5136_, 1);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_a_5136_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5140_ = v_a_5136_;
v_isShared_5141_ = v_isSharedCheck_5253_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_snd_5138_);
lean_inc(v_fst_5137_);
lean_dec(v_a_5136_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5253_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5115_, v_a_4701_, v_snd_5138_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v_fst_5144_; lean_object* v_snd_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5244_; 
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5142_, 1);
v_fst_5144_ = lean_ctor_get(v_a_5143_, 0);
v_snd_5145_ = lean_ctor_get(v_a_5143_, 1);
v_isSharedCheck_5244_ = !lean_is_exclusive(v_a_5143_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5147_ = v_a_5143_;
v_isShared_5148_ = v_isSharedCheck_5244_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_snd_5145_);
lean_inc(v_fst_5144_);
lean_dec(v_a_5143_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5244_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_LeanExport_dumpExpr(v_type_5116_, v_a_4701_, v_snd_5145_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; lean_object* v_fst_5151_; lean_object* v_snd_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5235_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v_fst_5151_ = lean_ctor_get(v_a_5150_, 0);
v_snd_5152_ = lean_ctor_get(v_a_5150_, 1);
v_isSharedCheck_5235_ = !lean_is_exclusive(v_a_5150_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5154_ = v_a_5150_;
v_isShared_5155_ = v_isSharedCheck_5235_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_snd_5152_);
lean_inc(v_fst_5151_);
lean_dec(v_a_5150_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5235_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5156_; 
v___x_5156_ = l_LeanExport_dumpExpr(v_value_5112_, v_a_4701_, v_snd_5152_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; lean_object* v_fst_5158_; lean_object* v_snd_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5226_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_a_5157_);
lean_dec_ref_known(v___x_5156_, 1);
v_fst_5158_ = lean_ctor_get(v_a_5157_, 0);
v_snd_5159_ = lean_ctor_get(v_a_5157_, 1);
v_isSharedCheck_5226_ = !lean_is_exclusive(v_a_5157_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5161_ = v_a_5157_;
v_isShared_5162_ = v_isSharedCheck_5226_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_snd_5159_);
lean_inc(v_fst_5158_);
lean_dec(v_a_5157_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5226_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5163_; 
v___x_5163_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5113_, v_a_4701_, v_snd_5159_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; lean_object* v_fst_5165_; lean_object* v_snd_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5217_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc(v_a_5164_);
lean_dec_ref_known(v___x_5163_, 1);
v_fst_5165_ = lean_ctor_get(v_a_5164_, 0);
v_snd_5166_ = lean_ctor_get(v_a_5164_, 1);
v_isSharedCheck_5217_ = !lean_is_exclusive(v_a_5164_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5168_ = v_a_5164_;
v_isShared_5169_ = v_isSharedCheck_5217_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_snd_5166_);
lean_inc(v_fst_5165_);
lean_dec(v_a_5164_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5217_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5174_; 
v___x_5170_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5172_ = l_Lean_JsonNumber_fromNat(v_fst_5137_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set_tag(v___x_5129_, 2);
lean_ctor_set(v___x_5129_, 0, v___x_5172_);
v___x_5174_ = v___x_5129_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5172_);
v___x_5174_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5176_; 
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 1, v___x_5174_);
lean_ctor_set(v___x_5168_, 0, v___x_5171_);
v___x_5176_ = v___x_5168_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5215_, 1, v___x_5174_);
v___x_5176_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
lean_object* v___x_5177_; lean_object* v___x_5179_; 
v___x_5177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 1, v_fst_5144_);
lean_ctor_set(v___x_5161_, 0, v___x_5177_);
v___x_5179_ = v___x_5161_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5214_, 1, v_fst_5144_);
v___x_5179_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5183_; 
v___x_5180_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5181_ = l_Lean_JsonNumber_fromNat(v_fst_5151_);
if (v_isShared_5121_ == 0)
{
lean_ctor_set_tag(v___x_5120_, 2);
lean_ctor_set(v___x_5120_, 0, v___x_5181_);
v___x_5183_ = v___x_5120_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5181_);
v___x_5183_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
lean_object* v___x_5185_; 
if (v_isShared_5155_ == 0)
{
lean_ctor_set(v___x_5154_, 1, v___x_5183_);
lean_ctor_set(v___x_5154_, 0, v___x_5180_);
v___x_5185_ = v___x_5154_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5180_);
lean_ctor_set(v_reuseFailAlloc_5212_, 1, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5189_; 
v___x_5186_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5187_ = l_Lean_JsonNumber_fromNat(v_fst_5158_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 0, v___x_5187_);
v___x_5189_ = v___x_5109_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5187_);
v___x_5189_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
lean_object* v___x_5191_; 
if (v_isShared_5148_ == 0)
{
lean_ctor_set(v___x_5147_, 1, v___x_5189_);
lean_ctor_set(v___x_5147_, 0, v___x_5186_);
v___x_5191_ = v___x_5147_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5186_);
lean_ctor_set(v_reuseFailAlloc_5210_, 1, v___x_5189_);
v___x_5191_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5192_; lean_object* v___x_5194_; 
v___x_5192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 1, v_fst_5165_);
lean_ctor_set(v___x_5140_, 0, v___x_5192_);
v___x_5194_ = v___x_5140_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5192_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v_fst_5165_);
v___x_5194_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
lean_object* v___x_5195_; lean_object* v___x_5197_; 
v___x_5195_ = lean_box(0);
if (v_isShared_5125_ == 0)
{
lean_ctor_set_tag(v___x_5124_, 1);
lean_ctor_set(v___x_5124_, 1, v___x_5195_);
lean_ctor_set(v___x_5124_, 0, v___x_5194_);
v___x_5197_ = v___x_5124_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5194_);
lean_ctor_set(v_reuseFailAlloc_5208_, 1, v___x_5195_);
v___x_5197_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5204_; 
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5191_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5185_);
lean_ctor_set(v___x_5199_, 1, v___x_5198_);
v___x_5200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5179_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5176_);
lean_ctor_set(v___x_5201_, 1, v___x_5200_);
v___x_5202_ = l_Lean_Json_mkObj(v___x_5201_);
lean_dec_ref_known(v___x_5201_, 2);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 1, v___x_5202_);
lean_ctor_set(v___x_5133_, 0, v___x_5170_);
v___x_5204_ = v___x_5133_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v___x_5170_);
lean_ctor_set(v_reuseFailAlloc_5207_, 1, v___x_5202_);
v___x_5204_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
lean_ctor_set(v___x_5205_, 1, v___x_5195_);
v___x_5206_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5205_, v_snd_5166_);
lean_dec_ref_known(v___x_5205_, 2);
return v___x_5206_;
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
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_del_object(v___x_5161_);
lean_dec(v_fst_5158_);
lean_del_object(v___x_5154_);
lean_dec(v_fst_5151_);
lean_del_object(v___x_5147_);
lean_dec(v_fst_5144_);
lean_del_object(v___x_5140_);
lean_dec(v_fst_5137_);
lean_del_object(v___x_5133_);
lean_del_object(v___x_5129_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5109_);
v_a_5218_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5163_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5163_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5234_; 
lean_del_object(v___x_5154_);
lean_dec(v_fst_5151_);
lean_del_object(v___x_5147_);
lean_dec(v_fst_5144_);
lean_del_object(v___x_5140_);
lean_dec(v_fst_5137_);
lean_del_object(v___x_5133_);
lean_del_object(v___x_5129_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_dec(v_all_5113_);
lean_del_object(v___x_5109_);
v_a_5227_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5156_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5156_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_del_object(v___x_5147_);
lean_dec(v_fst_5144_);
lean_del_object(v___x_5140_);
lean_dec(v_fst_5137_);
lean_del_object(v___x_5133_);
lean_del_object(v___x_5129_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_dec(v_all_5113_);
lean_dec_ref(v_value_5112_);
lean_del_object(v___x_5109_);
v_a_5236_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5149_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5149_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_del_object(v___x_5140_);
lean_dec(v_fst_5137_);
lean_del_object(v___x_5133_);
lean_del_object(v___x_5129_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_dec_ref(v_type_5116_);
lean_dec(v_all_5113_);
lean_dec_ref(v_value_5112_);
lean_del_object(v___x_5109_);
v_a_5245_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5142_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5142_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_del_object(v___x_5133_);
lean_del_object(v___x_5129_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_dec_ref(v_type_5116_);
lean_dec(v_levelParams_5115_);
lean_dec(v_all_5113_);
lean_dec_ref(v_value_5112_);
lean_del_object(v___x_5109_);
v_a_5254_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5135_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5135_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_dec_ref(v_type_5116_);
lean_dec(v_levelParams_5115_);
lean_dec(v_name_5114_);
lean_dec(v_all_5113_);
lean_dec_ref(v_value_5112_);
lean_del_object(v___x_5109_);
return v___x_5126_;
}
}
}
}
else
{
lean_dec_ref(v_type_5116_);
lean_dec(v_levelParams_5115_);
lean_dec(v_name_5114_);
lean_dec(v_all_5113_);
lean_dec_ref(v_value_5112_);
lean_del_object(v___x_5109_);
return v___x_5117_;
}
}
}
case 3:
{
lean_object* v_val_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5435_; 
v_val_5269_ = lean_ctor_get(v_val_4812_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_val_4812_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5271_ = v_val_4812_;
v_isShared_5272_ = v_isSharedCheck_5435_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_val_5269_);
lean_dec(v_val_4812_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5435_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v_toConstantVal_5273_; lean_object* v_value_5274_; uint8_t v_isUnsafe_5275_; lean_object* v_all_5276_; lean_object* v_name_5277_; lean_object* v_levelParams_5278_; lean_object* v_type_5279_; lean_object* v___x_5280_; 
v_toConstantVal_5273_ = lean_ctor_get(v_val_5269_, 0);
lean_inc_ref(v_toConstantVal_5273_);
v_value_5274_ = lean_ctor_get(v_val_5269_, 1);
lean_inc_ref(v_value_5274_);
v_isUnsafe_5275_ = lean_ctor_get_uint8(v_val_5269_, sizeof(void*)*3);
v_all_5276_ = lean_ctor_get(v_val_5269_, 2);
lean_inc(v_all_5276_);
lean_dec_ref(v_val_5269_);
v_name_5277_ = lean_ctor_get(v_toConstantVal_5273_, 0);
lean_inc(v_name_5277_);
v_levelParams_5278_ = lean_ctor_get(v_toConstantVal_5273_, 1);
lean_inc(v_levelParams_5278_);
v_type_5279_ = lean_ctor_get(v_toConstantVal_5273_, 2);
lean_inc_ref_n(v_type_5279_, 2);
lean_dec_ref(v_toConstantVal_5273_);
v___x_5280_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5279_, v_a_4701_, v___x_4829_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5434_; 
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5283_ = v___x_5280_;
v_isShared_5284_ = v_isSharedCheck_5434_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5280_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5434_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v_snd_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5432_; 
v_snd_5285_ = lean_ctor_get(v_a_5281_, 1);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_a_5281_);
if (v_isSharedCheck_5432_ == 0)
{
lean_object* v_unused_5433_; 
v_unused_5433_ = lean_ctor_get(v_a_5281_, 0);
lean_dec(v_unused_5433_);
v___x_5287_ = v_a_5281_;
v_isShared_5288_ = v_isSharedCheck_5432_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_snd_5285_);
lean_dec(v_a_5281_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5432_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; 
lean_inc_ref(v_value_5274_);
v___x_5289_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5274_, v_a_4701_, v_snd_5285_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5431_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5292_ = v___x_5289_;
v_isShared_5293_ = v_isSharedCheck_5431_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5289_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5431_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v_snd_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5429_; 
v_snd_5294_ = lean_ctor_get(v_a_5290_, 1);
v_isSharedCheck_5429_ = !lean_is_exclusive(v_a_5290_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; 
v_unused_5430_ = lean_ctor_get(v_a_5290_, 0);
lean_dec(v_unused_5430_);
v___x_5296_ = v_a_5290_;
v_isShared_5297_ = v_isSharedCheck_5429_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_snd_5294_);
lean_dec(v_a_5290_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5429_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5298_; 
v___x_5298_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5277_, v_a_4701_, v_snd_5294_);
if (lean_obj_tag(v___x_5298_) == 0)
{
lean_object* v_a_5299_; lean_object* v_fst_5300_; lean_object* v_snd_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5420_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref_known(v___x_5298_, 1);
v_fst_5300_ = lean_ctor_get(v_a_5299_, 0);
v_snd_5301_ = lean_ctor_get(v_a_5299_, 1);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_a_5299_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5303_ = v_a_5299_;
v_isShared_5304_ = v_isSharedCheck_5420_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_snd_5301_);
lean_inc(v_fst_5300_);
lean_dec(v_a_5299_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5420_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5305_; 
v___x_5305_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5278_, v_a_4701_, v_snd_5301_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v_fst_5307_; lean_object* v_snd_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5411_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref_known(v___x_5305_, 1);
v_fst_5307_ = lean_ctor_get(v_a_5306_, 0);
v_snd_5308_ = lean_ctor_get(v_a_5306_, 1);
v_isSharedCheck_5411_ = !lean_is_exclusive(v_a_5306_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5310_ = v_a_5306_;
v_isShared_5311_ = v_isSharedCheck_5411_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_snd_5308_);
lean_inc(v_fst_5307_);
lean_dec(v_a_5306_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5411_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5312_; 
v___x_5312_ = l_LeanExport_dumpExpr(v_type_5279_, v_a_4701_, v_snd_5308_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v_fst_5314_; lean_object* v_snd_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5402_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v_a_5313_);
lean_dec_ref_known(v___x_5312_, 1);
v_fst_5314_ = lean_ctor_get(v_a_5313_, 0);
v_snd_5315_ = lean_ctor_get(v_a_5313_, 1);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_a_5313_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5317_ = v_a_5313_;
v_isShared_5318_ = v_isSharedCheck_5402_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_snd_5315_);
lean_inc(v_fst_5314_);
lean_dec(v_a_5313_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5402_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5319_; 
v___x_5319_ = l_LeanExport_dumpExpr(v_value_5274_, v_a_4701_, v_snd_5315_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_object* v_a_5320_; lean_object* v_fst_5321_; lean_object* v_snd_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5393_; 
v_a_5320_ = lean_ctor_get(v___x_5319_, 0);
lean_inc(v_a_5320_);
lean_dec_ref_known(v___x_5319_, 1);
v_fst_5321_ = lean_ctor_get(v_a_5320_, 0);
v_snd_5322_ = lean_ctor_get(v_a_5320_, 1);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_a_5320_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5324_ = v_a_5320_;
v_isShared_5325_ = v_isSharedCheck_5393_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_snd_5322_);
lean_inc(v_fst_5321_);
lean_dec(v_a_5320_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5393_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5326_; 
v___x_5326_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5276_, v_a_4701_, v_snd_5322_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v_fst_5328_; lean_object* v_snd_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5384_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_a_5327_);
lean_dec_ref_known(v___x_5326_, 1);
v_fst_5328_ = lean_ctor_get(v_a_5327_, 0);
v_snd_5329_ = lean_ctor_get(v_a_5327_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_a_5327_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5331_ = v_a_5327_;
v_isShared_5332_ = v_isSharedCheck_5384_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_snd_5329_);
lean_inc(v_fst_5328_);
lean_dec(v_a_5327_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5384_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5337_; 
v___x_5333_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__0));
v___x_5335_ = l_Lean_JsonNumber_fromNat(v_fst_5300_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set_tag(v___x_5292_, 2);
lean_ctor_set(v___x_5292_, 0, v___x_5335_);
v___x_5337_ = v___x_5292_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5339_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 1, v___x_5337_);
lean_ctor_set(v___x_5331_, 0, v___x_5334_);
v___x_5339_ = v___x_5331_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5334_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v___x_5337_);
v___x_5339_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
lean_object* v___x_5340_; lean_object* v___x_5342_; 
v___x_5340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__1));
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 1, v_fst_5307_);
lean_ctor_set(v___x_5324_, 0, v___x_5340_);
v___x_5342_ = v___x_5324_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5340_);
lean_ctor_set(v_reuseFailAlloc_5381_, 1, v_fst_5307_);
v___x_5342_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5346_; 
v___x_5343_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5344_ = l_Lean_JsonNumber_fromNat(v_fst_5314_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set_tag(v___x_5283_, 2);
lean_ctor_set(v___x_5283_, 0, v___x_5344_);
v___x_5346_ = v___x_5283_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5344_);
v___x_5346_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5348_; 
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 1, v___x_5346_);
lean_ctor_set(v___x_5317_, 0, v___x_5343_);
v___x_5348_ = v___x_5317_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v___x_5346_);
v___x_5348_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5352_; 
v___x_5349_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5350_ = l_Lean_JsonNumber_fromNat(v_fst_5321_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set_tag(v___x_5271_, 2);
lean_ctor_set(v___x_5271_, 0, v___x_5350_);
v___x_5352_ = v___x_5271_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5350_);
v___x_5352_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
lean_object* v___x_5354_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 1, v___x_5352_);
lean_ctor_set(v___x_5310_, 0, v___x_5349_);
v___x_5354_ = v___x_5310_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5377_, 1, v___x_5352_);
v___x_5354_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 1, v_fst_5328_);
lean_ctor_set(v___x_5303_, 0, v___x_5355_);
v___x_5357_ = v___x_5303_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v_fst_5328_);
v___x_5357_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___closed__6));
v___x_5359_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5359_, 0, v_isUnsafe_5275_);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 1, v___x_5359_);
lean_ctor_set(v___x_5296_, 0, v___x_5358_);
v___x_5361_ = v___x_5296_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5375_, 1, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5371_; 
v___x_5362_ = lean_box(0);
v___x_5363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5361_);
lean_ctor_set(v___x_5363_, 1, v___x_5362_);
v___x_5364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5364_, 0, v___x_5357_);
lean_ctor_set(v___x_5364_, 1, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5354_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
v___x_5366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5348_);
lean_ctor_set(v___x_5366_, 1, v___x_5365_);
v___x_5367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5342_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5339_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
v___x_5369_ = l_Lean_Json_mkObj(v___x_5368_);
lean_dec_ref_known(v___x_5368_, 2);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 1, v___x_5369_);
lean_ctor_set(v___x_5287_, 0, v___x_5333_);
v___x_5371_ = v___x_5287_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5333_);
lean_ctor_set(v_reuseFailAlloc_5374_, 1, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5371_);
lean_ctor_set(v___x_5372_, 1, v___x_5362_);
v___x_5373_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5372_, v_snd_5329_);
lean_dec_ref_known(v___x_5372_, 2);
return v___x_5373_;
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
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_del_object(v___x_5324_);
lean_dec(v_fst_5321_);
lean_del_object(v___x_5317_);
lean_dec(v_fst_5314_);
lean_del_object(v___x_5310_);
lean_dec(v_fst_5307_);
lean_del_object(v___x_5303_);
lean_dec(v_fst_5300_);
lean_del_object(v___x_5296_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5271_);
v_a_5385_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5326_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5326_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_del_object(v___x_5317_);
lean_dec(v_fst_5314_);
lean_del_object(v___x_5310_);
lean_dec(v_fst_5307_);
lean_del_object(v___x_5303_);
lean_dec(v_fst_5300_);
lean_del_object(v___x_5296_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_dec(v_all_5276_);
lean_del_object(v___x_5271_);
v_a_5394_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5319_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5319_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_del_object(v___x_5310_);
lean_dec(v_fst_5307_);
lean_del_object(v___x_5303_);
lean_dec(v_fst_5300_);
lean_del_object(v___x_5296_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_dec(v_all_5276_);
lean_dec_ref(v_value_5274_);
lean_del_object(v___x_5271_);
v_a_5403_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5312_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5312_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5419_; 
lean_del_object(v___x_5303_);
lean_dec(v_fst_5300_);
lean_del_object(v___x_5296_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_dec_ref(v_type_5279_);
lean_dec(v_all_5276_);
lean_dec_ref(v_value_5274_);
lean_del_object(v___x_5271_);
v_a_5412_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5305_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5305_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5417_; 
if (v_isShared_5415_ == 0)
{
v___x_5417_ = v___x_5414_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5412_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
lean_del_object(v___x_5296_);
lean_del_object(v___x_5292_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_dec_ref(v_type_5279_);
lean_dec(v_levelParams_5278_);
lean_dec(v_all_5276_);
lean_dec_ref(v_value_5274_);
lean_del_object(v___x_5271_);
v_a_5421_ = lean_ctor_get(v___x_5298_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5298_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5298_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5298_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_dec_ref(v_type_5279_);
lean_dec(v_levelParams_5278_);
lean_dec(v_name_5277_);
lean_dec(v_all_5276_);
lean_dec_ref(v_value_5274_);
lean_del_object(v___x_5271_);
return v___x_5289_;
}
}
}
}
else
{
lean_dec_ref(v_type_5279_);
lean_dec(v_levelParams_5278_);
lean_dec(v_name_5277_);
lean_dec(v_all_5276_);
lean_dec_ref(v_value_5274_);
lean_del_object(v___x_5271_);
return v___x_5280_;
}
}
}
case 4:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; 
lean_dec_ref_known(v_val_4812_, 1);
v___x_5436_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5437_ = l_LeanExport_dumpConstant(v___x_5436_, v_a_4701_, v___x_4829_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_object* v_a_5438_; lean_object* v_snd_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; 
v_a_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc(v_a_5438_);
lean_dec_ref_known(v___x_5437_, 1);
v_snd_5439_ = lean_ctor_get(v_a_5438_, 1);
lean_inc(v_snd_5439_);
lean_dec(v_a_5438_);
v___x_5440_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5441_ = lean_box(0);
v___x_5442_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5443_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4823_, v___x_5440_, v___x_5442_, v_a_4701_, v_snd_5439_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5470_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5446_ = v___x_5443_;
v_isShared_5447_ = v_isSharedCheck_5470_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_a_5444_);
lean_dec(v___x_5443_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5470_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v_fst_5448_; lean_object* v_fst_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5468_; 
v_fst_5448_ = lean_ctor_get(v_a_5444_, 0);
lean_inc(v_fst_5448_);
v_fst_5449_ = lean_ctor_get(v_fst_5448_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v_fst_5448_);
if (v_isSharedCheck_5468_ == 0)
{
lean_object* v_unused_5469_; 
v_unused_5469_ = lean_ctor_get(v_fst_5448_, 1);
lean_dec(v_unused_5469_);
v___x_5451_ = v_fst_5448_;
v_isShared_5452_ = v_isSharedCheck_5468_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_fst_5449_);
lean_dec(v_fst_5448_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5468_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
if (lean_obj_tag(v_fst_5449_) == 0)
{
lean_object* v_snd_5453_; lean_object* v___x_5455_; 
v_snd_5453_ = lean_ctor_get(v_a_5444_, 1);
lean_inc(v_snd_5453_);
lean_dec(v_a_5444_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 1, v_snd_5453_);
lean_ctor_set(v___x_5451_, 0, v___x_5441_);
v___x_5455_ = v___x_5451_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v_snd_5453_);
v___x_5455_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5457_; 
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 0, v___x_5455_);
v___x_5457_ = v___x_5446_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
else
{
lean_object* v_snd_5460_; lean_object* v_val_5461_; lean_object* v___x_5463_; 
v_snd_5460_ = lean_ctor_get(v_a_5444_, 1);
lean_inc(v_snd_5460_);
lean_dec(v_a_5444_);
v_val_5461_ = lean_ctor_get(v_fst_5449_, 0);
lean_inc(v_val_5461_);
lean_dec_ref_known(v_fst_5449_, 1);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 1, v_snd_5460_);
lean_ctor_set(v___x_5451_, 0, v_val_5461_);
v___x_5463_ = v___x_5451_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_val_5461_);
lean_ctor_set(v_reuseFailAlloc_5467_, 1, v_snd_5460_);
v___x_5463_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
lean_object* v___x_5465_; 
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 0, v___x_5463_);
v___x_5465_ = v___x_5446_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
}
}
else
{
lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
v_a_5471_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5443_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5443_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
else
{
return v___x_5437_;
}
}
case 5:
{
lean_object* v_val_5479_; lean_object* v_all_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v_val_5479_ = lean_ctor_get(v_val_4812_, 0);
lean_inc_ref(v_val_5479_);
lean_dec_ref_known(v_val_4812_, 1);
v_all_5480_ = lean_ctor_get(v_val_5479_, 3);
lean_inc(v_all_5480_);
v___x_5481_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5482_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5483_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4823_, v_val_5479_, v_all_5480_, v___x_5482_, v_a_4701_, v___x_4829_);
lean_dec(v_all_5480_);
lean_dec_ref(v_val_5479_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v_a_5484_; lean_object* v_fst_5485_; lean_object* v_snd_5486_; lean_object* v_snd_5487_; lean_object* v_fst_5488_; lean_object* v_fst_5489_; lean_object* v_snd_5490_; lean_object* v___x_5491_; size_t v_sz_5492_; size_t v___x_5493_; lean_object* v___x_5494_; 
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_a_5484_);
lean_dec_ref_known(v___x_5483_, 1);
v_fst_5485_ = lean_ctor_get(v_a_5484_, 0);
lean_inc(v_fst_5485_);
v_snd_5486_ = lean_ctor_get(v_fst_5485_, 1);
lean_inc(v_snd_5486_);
v_snd_5487_ = lean_ctor_get(v_a_5484_, 1);
lean_inc(v_snd_5487_);
lean_dec(v_a_5484_);
v_fst_5488_ = lean_ctor_get(v_fst_5485_, 0);
lean_inc(v_fst_5488_);
lean_dec(v_fst_5485_);
v_fst_5489_ = lean_ctor_get(v_snd_5486_, 0);
lean_inc(v_fst_5489_);
v_snd_5490_ = lean_ctor_get(v_snd_5486_, 1);
lean_inc(v_snd_5490_);
lean_dec(v_snd_5486_);
v___x_5491_ = lean_box(0);
v_sz_5492_ = lean_array_size(v_fst_5489_);
v___x_5493_ = ((size_t)0ULL);
v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_5489_, v_sz_5492_, v___x_5493_, v___x_5491_, v_a_4701_, v_snd_5487_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v_snd_5496_; lean_object* v___x_5497_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v___x_5494_, 1);
v_snd_5496_ = lean_ctor_get(v_a_5495_, 1);
lean_inc(v_snd_5496_);
lean_dec(v_a_5495_);
v___x_5497_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15(v___x_4823_, v___x_5481_, v_snd_5490_, v_a_4701_, v_snd_5496_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v_fst_5499_; lean_object* v_snd_5500_; lean_object* v_a_5501_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref_known(v___x_5497_, 1);
v_fst_5499_ = lean_ctor_get(v_a_5498_, 0);
lean_inc(v_fst_5499_);
v_snd_5500_ = lean_ctor_get(v_a_5498_, 1);
lean_inc(v_snd_5500_);
lean_dec(v_a_5498_);
v_a_5501_ = lean_ctor_get(v_fst_5499_, 0);
lean_inc(v_a_5501_);
lean_dec(v_fst_5499_);
v___y_4709_ = v_fst_5488_;
v___y_4710_ = v___x_5491_;
v___y_4711_ = v_sz_5492_;
v___y_4712_ = v_fst_5489_;
v___y_4713_ = v___x_5493_;
v_fst_4714_ = v_a_5501_;
v_snd_4715_ = v_snd_5500_;
goto v___jp_4708_;
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_fst_5489_);
lean_dec(v_fst_5488_);
v_a_5502_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5497_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5497_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
else
{
lean_dec(v_snd_5490_);
lean_dec(v_fst_5489_);
lean_dec(v_fst_5488_);
return v___x_5494_;
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
v_a_5510_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5483_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5483_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
case 6:
{
lean_object* v_val_5518_; lean_object* v_induct_5519_; 
v_val_5518_ = lean_ctor_get(v_val_4812_, 0);
lean_inc_ref(v_val_5518_);
lean_dec_ref_known(v_val_4812_, 1);
v_induct_5519_ = lean_ctor_get(v_val_5518_, 1);
lean_inc(v_induct_5519_);
lean_dec_ref(v_val_5518_);
v_c_4700_ = v_induct_5519_;
v_a_4702_ = v___x_4829_;
goto _start;
}
default: 
{
lean_object* v_val_5521_; lean_object* v_all_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; 
v_val_5521_ = lean_ctor_get(v_val_4812_, 0);
lean_inc_ref(v_val_5521_);
lean_dec_ref_known(v_val_4812_, 1);
v_all_5522_ = lean_ctor_get(v_val_5521_, 1);
lean_inc(v_all_5522_);
lean_dec_ref(v_val_5521_);
v___x_5523_ = lean_box(0);
v___x_5524_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5522_, v___x_5523_, v_a_4701_, v___x_4829_);
lean_dec(v_all_5522_);
if (lean_obj_tag(v___x_5524_) == 0)
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5541_; 
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5527_ = v___x_5524_;
v_isShared_5528_ = v_isSharedCheck_5541_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5524_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5541_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v_snd_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5539_; 
v_snd_5529_ = lean_ctor_get(v_a_5525_, 1);
v_isSharedCheck_5539_ = !lean_is_exclusive(v_a_5525_);
if (v_isSharedCheck_5539_ == 0)
{
lean_object* v_unused_5540_; 
v_unused_5540_ = lean_ctor_get(v_a_5525_, 0);
lean_dec(v_unused_5540_);
v___x_5531_ = v_a_5525_;
v_isShared_5532_ = v_isSharedCheck_5539_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_snd_5529_);
lean_dec(v_a_5525_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5539_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5534_; 
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 0, v___x_5523_);
v___x_5534_ = v___x_5531_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v_snd_5529_);
v___x_5534_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5536_; 
if (v_isShared_5528_ == 0)
{
lean_ctor_set(v___x_5527_, 0, v___x_5534_);
v___x_5536_ = v___x_5527_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
}
else
{
return v___x_5524_;
}
}
}
}
}
}
else
{
lean_dec(v_val_4812_);
lean_dec(v_c_4700_);
goto v___jp_4704_;
}
}
v___jp_5550_:
{
if (v___y_5551_ == 0)
{
goto v___jp_4813_;
}
else
{
lean_dec(v_val_4812_);
lean_dec(v_c_4700_);
goto v___jp_4704_;
}
}
}
else
{
uint8_t v_ignoreMissing_5554_; 
lean_dec(v___x_4811_);
v_ignoreMissing_5554_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5554_ == 0)
{
lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; uint8_t v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5555_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5556_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__15___closed__0));
v___x_5557_ = lean_unsigned_to_nat(254u);
v___x_5558_ = lean_unsigned_to_nat(48u);
v___x_5559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5560_ = 1;
v___x_5561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4700_, v___x_5560_);
v___x_5562_ = lean_string_append(v___x_5559_, v___x_5561_);
lean_dec_ref(v___x_5561_);
v___x_5563_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5564_ = lean_string_append(v___x_5562_, v___x_5563_);
v___x_5565_ = l_mkPanicMessageWithDecl(v___x_5555_, v___x_5556_, v___x_5557_, v___x_5558_, v___x_5564_);
lean_dec_ref(v___x_5564_);
v___x_5566_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5565_, v_a_4701_, v_a_4702_);
return v___x_5566_;
}
else
{
lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
lean_dec(v_c_4700_);
v___x_5567_ = lean_box(0);
v___x_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
lean_ctor_set(v___x_5568_, 1, v_a_4702_);
v___x_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
return v___x_5569_;
}
}
v___jp_4704_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4705_ = lean_box(0);
v___x_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set(v___x_4706_, 1, v_a_4702_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
return v___x_4707_;
}
v___jp_4708_:
{
size_t v_sz_4716_; lean_object* v___x_4717_; 
v_sz_4716_ = lean_array_size(v_fst_4714_);
v___x_4717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(v_fst_4714_, v_sz_4716_, v___y_4713_, v___y_4710_, v_a_4701_, v_snd_4715_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v_snd_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4808_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4717_, 1);
v_snd_4719_ = lean_ctor_get(v_a_4718_, 1);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_a_4718_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v_a_4718_, 0);
lean_dec(v_unused_4809_);
v___x_4721_ = v_a_4718_;
v_isShared_4722_ = v_isSharedCheck_4808_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_snd_4719_);
lean_dec(v_a_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4808_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4723_; 
v___x_4723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(v_fst_4714_, v_sz_4716_, v___y_4713_, v___y_4710_, v_a_4701_, v_snd_4719_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v_snd_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4806_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v_snd_4725_ = lean_ctor_get(v_a_4724_, 1);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_a_4724_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v_a_4724_, 0);
lean_dec(v_unused_4807_);
v___x_4727_ = v_a_4724_;
v_isShared_4728_ = v_isSharedCheck_4806_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_snd_4725_);
lean_dec(v_a_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4806_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
size_t v_sz_4729_; lean_object* v___x_4730_; 
v_sz_4729_ = lean_array_size(v___y_4709_);
v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4729_, v___y_4713_, v___y_4709_, v_a_4701_, v_snd_4725_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v_fst_4732_; lean_object* v_snd_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4797_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v_fst_4732_ = lean_ctor_get(v_a_4731_, 0);
v_snd_4733_ = lean_ctor_get(v_a_4731_, 1);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_a_4731_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4735_ = v_a_4731_;
v_isShared_4736_ = v_isSharedCheck_4797_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_snd_4733_);
lean_inc(v_fst_4732_);
lean_dec(v_a_4731_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4797_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; 
v___x_4737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(v___y_4711_, v___y_4713_, v___y_4712_, v_a_4701_, v_snd_4733_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v_fst_4739_; lean_object* v_snd_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4788_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v_fst_4739_ = lean_ctor_get(v_a_4738_, 0);
v_snd_4740_ = lean_ctor_get(v_a_4738_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_a_4738_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4742_ = v_a_4738_;
v_isShared_4743_ = v_isSharedCheck_4788_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_snd_4740_);
lean_inc(v_fst_4739_);
lean_dec(v_a_4738_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4788_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4744_; 
v___x_4744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(v_sz_4716_, v___y_4713_, v_fst_4714_, v_a_4701_, v_snd_4740_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v_fst_4746_; lean_object* v_snd_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4779_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v_fst_4746_ = lean_ctor_get(v_a_4745_, 0);
v_snd_4747_ = lean_ctor_get(v_a_4745_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_a_4745_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4749_ = v_a_4745_;
v_isShared_4750_ = v_isSharedCheck_4779_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_snd_4747_);
lean_inc(v_fst_4746_);
lean_dec(v_a_4745_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4779_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4755_; 
v___x_4751_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4752_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4753_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4732_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 1, v___x_4753_);
lean_ctor_set(v___x_4749_, 0, v___x_4752_);
v___x_4755_ = v___x_4749_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4752_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4759_; 
v___x_4756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4757_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4739_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 1, v___x_4757_);
lean_ctor_set(v___x_4742_, 0, v___x_4756_);
v___x_4759_ = v___x_4742_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4777_, 1, v___x_4757_);
v___x_4759_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
v___x_4760_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4761_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__21(v_fst_4746_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 1, v___x_4761_);
lean_ctor_set(v___x_4735_, 0, v___x_4760_);
v___x_4763_ = v___x_4735_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4764_ = lean_box(0);
if (v_isShared_4722_ == 0)
{
lean_ctor_set_tag(v___x_4721_, 1);
lean_ctor_set(v___x_4721_, 1, v___x_4764_);
lean_ctor_set(v___x_4721_, 0, v___x_4763_);
v___x_4766_ = v___x_4721_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4763_);
lean_ctor_set(v_reuseFailAlloc_4775_, 1, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4759_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4755_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = l_Lean_Json_mkObj(v___x_4768_);
lean_dec_ref_known(v___x_4768_, 2);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 1, v___x_4769_);
lean_ctor_set(v___x_4727_, 0, v___x_4751_);
v___x_4771_ = v___x_4727_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v___x_4769_);
v___x_4771_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
lean_ctor_set(v___x_4772_, 1, v___x_4764_);
v___x_4773_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4772_, v_snd_4747_);
lean_dec_ref_known(v___x_4772_, 2);
return v___x_4773_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_del_object(v___x_4742_);
lean_dec(v_fst_4739_);
lean_del_object(v___x_4735_);
lean_dec(v_fst_4732_);
lean_del_object(v___x_4727_);
lean_del_object(v___x_4721_);
v_a_4780_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4744_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4744_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
else
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
lean_del_object(v___x_4735_);
lean_dec(v_fst_4732_);
lean_del_object(v___x_4727_);
lean_del_object(v___x_4721_);
lean_dec_ref(v_fst_4714_);
v_a_4789_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4737_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4737_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_del_object(v___x_4727_);
lean_del_object(v___x_4721_);
lean_dec_ref(v_fst_4714_);
lean_dec(v___y_4712_);
v_a_4798_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4730_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4730_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
else
{
lean_del_object(v___x_4721_);
lean_dec_ref(v_fst_4714_);
lean_dec(v___y_4712_);
lean_dec(v___y_4709_);
return v___x_4723_;
}
}
}
else
{
lean_dec_ref(v_fst_4714_);
lean_dec(v___y_4712_);
lean_dec(v___y_4709_);
return v___x_4717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5570_, size_t v_sz_5571_, size_t v_i_5572_, lean_object* v_b_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
uint8_t v___x_5577_; 
v___x_5577_ = lean_usize_dec_lt(v_i_5572_, v_sz_5571_);
if (v___x_5577_ == 0)
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5578_, 0, v_b_5573_);
lean_ctor_set(v___x_5578_, 1, v___y_5575_);
v___x_5579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
return v___x_5579_;
}
else
{
lean_object* v_a_5580_; lean_object* v___x_5581_; 
v_a_5580_ = lean_array_uget_borrowed(v_as_5570_, v_i_5572_);
lean_inc(v_a_5580_);
v___x_5581_ = l_LeanExport_dumpConstant(v_a_5580_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v_snd_5583_; lean_object* v___x_5584_; size_t v___x_5585_; size_t v___x_5586_; 
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v___x_5581_, 1);
v_snd_5583_ = lean_ctor_get(v_a_5582_, 1);
lean_inc(v_snd_5583_);
lean_dec(v_a_5582_);
v___x_5584_ = lean_box(0);
v___x_5585_ = ((size_t)1ULL);
v___x_5586_ = lean_usize_add(v_i_5572_, v___x_5585_);
v_i_5572_ = v___x_5586_;
v_b_5573_ = v___x_5584_;
v___y_5575_ = v_snd_5583_;
goto _start;
}
else
{
return v___x_5581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_){
_start:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; size_t v_sz_5594_; size_t v___x_5595_; lean_object* v___x_5596_; 
v___x_5592_ = l_Lean_Expr_getUsedConstants(v_e_5588_);
v___x_5593_ = lean_box(0);
v_sz_5594_ = lean_array_size(v___x_5592_);
v___x_5595_ = ((size_t)0ULL);
v___x_5596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5592_, v_sz_5594_, v___x_5595_, v___x_5593_, v_a_5589_, v_a_5590_);
lean_dec_ref(v___x_5592_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5613_; 
v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5599_ = v___x_5596_;
v_isShared_5600_ = v_isSharedCheck_5613_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5596_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5613_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v_snd_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5611_; 
v_snd_5601_ = lean_ctor_get(v_a_5597_, 1);
v_isSharedCheck_5611_ = !lean_is_exclusive(v_a_5597_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; 
v_unused_5612_ = lean_ctor_get(v_a_5597_, 0);
lean_dec(v_unused_5612_);
v___x_5603_ = v_a_5597_;
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_snd_5601_);
lean_dec(v_a_5597_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5611_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 0, v___x_5593_);
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_snd_5601_);
v___x_5606_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
lean_object* v___x_5608_; 
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 0, v___x_5606_);
v___x_5608_ = v___x_5599_;
goto v_reusejp_5607_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v___x_5606_);
v___x_5608_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5607_;
}
v_reusejp_5607_:
{
return v___x_5608_;
}
}
}
}
}
else
{
return v___x_5596_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5614_, v_a_5615_, v_a_5616_);
lean_dec_ref(v_a_5615_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5619_, lean_object* v_b_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5619_, v_b_5620_, v___y_5621_, v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec(v_as_x27_5619_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5625_, lean_object* v_b_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_){
_start:
{
lean_object* v_res_5630_; 
v_res_5630_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5625_, v_b_5626_, v___y_5627_, v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v_as_x27_5625_);
return v_res_5630_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5631_, lean_object* v_x_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5631_, v_x_5632_, v___y_5633_, v___y_5634_);
lean_dec_ref(v___y_5633_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5637_, lean_object* v_sz_5638_, lean_object* v_i_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_){
_start:
{
size_t v_sz_boxed_5644_; size_t v_i_boxed_5645_; lean_object* v_res_5646_; 
v_sz_boxed_5644_ = lean_unbox_usize(v_sz_5638_);
lean_dec(v_sz_5638_);
v_i_boxed_5645_ = lean_unbox_usize(v_i_5639_);
lean_dec(v_i_5639_);
v_res_5646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5637_, v_sz_boxed_5644_, v_i_boxed_5645_, v_b_5640_, v___y_5641_, v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec_ref(v_as_5637_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_){
_start:
{
lean_object* v_res_5650_; 
v_res_5650_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5647_, v_a_5648_);
lean_dec_ref(v_a_5647_);
return v_res_5650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_as_5651_, lean_object* v_sz_5652_, lean_object* v_i_5653_, lean_object* v_b_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
size_t v_sz_boxed_5658_; size_t v_i_boxed_5659_; lean_object* v_res_5660_; 
v_sz_boxed_5658_ = lean_unbox_usize(v_sz_5652_);
lean_dec(v_sz_5652_);
v_i_boxed_5659_ = lean_unbox_usize(v_i_5653_);
lean_dec(v_i_5653_);
v_res_5660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__17(v_as_5651_, v_sz_boxed_5658_, v_i_boxed_5659_, v_b_5654_, v___y_5655_, v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec_ref(v_as_5651_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l_LeanExport_dumpExpr(v_e_5661_, v_a_5662_, v_a_5663_);
lean_dec_ref(v_a_5662_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5666_, lean_object* v_sz_5667_, lean_object* v_i_5668_, lean_object* v_b_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_){
_start:
{
size_t v_sz_boxed_5673_; size_t v_i_boxed_5674_; lean_object* v_res_5675_; 
v_sz_boxed_5673_ = lean_unbox_usize(v_sz_5667_);
lean_dec(v_sz_5667_);
v_i_boxed_5674_ = lean_unbox_usize(v_i_5668_);
lean_dec(v_i_5668_);
v_res_5675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5666_, v_sz_boxed_5673_, v_i_boxed_5674_, v_b_5669_, v___y_5670_, v___y_5671_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v_as_5666_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_as_5676_, lean_object* v_sz_5677_, lean_object* v_i_5678_, lean_object* v_b_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
size_t v_sz_boxed_5683_; size_t v_i_boxed_5684_; lean_object* v_res_5685_; 
v_sz_boxed_5683_ = lean_unbox_usize(v_sz_5677_);
lean_dec(v_sz_5677_);
v_i_boxed_5684_ = lean_unbox_usize(v_i_5678_);
lean_dec(v_i_5678_);
v_res_5685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__16(v_as_5676_, v_sz_boxed_5683_, v_i_boxed_5684_, v_b_5679_, v___y_5680_, v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec_ref(v_as_5676_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_){
_start:
{
lean_object* v_res_5690_; 
v_res_5690_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5686_, v_a_5687_, v_a_5688_);
lean_dec_ref(v_a_5687_);
return v_res_5690_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5691_, v_a_5692_);
lean_dec_ref(v_a_5691_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19___boxed(lean_object* v_sz_5695_, lean_object* v_i_5696_, lean_object* v_bs_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
size_t v_sz_boxed_5701_; size_t v_i_boxed_5702_; lean_object* v_res_5703_; 
v_sz_boxed_5701_ = lean_unbox_usize(v_sz_5695_);
lean_dec(v_sz_5695_);
v_i_boxed_5702_ = lean_unbox_usize(v_i_5696_);
lean_dec(v_i_5696_);
v_res_5703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__19(v_sz_boxed_5701_, v_i_boxed_5702_, v_bs_5697_, v___y_5698_, v___y_5699_);
lean_dec_ref(v___y_5698_);
return v_res_5703_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5704_, lean_object* v_as_x27_5705_, lean_object* v_b_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
uint8_t v___x_173051__boxed_5710_; lean_object* v_res_5711_; 
v___x_173051__boxed_5710_ = lean_unbox(v___x_5704_);
v_res_5711_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173051__boxed_5710_, v_as_x27_5705_, v_b_5706_, v___y_5707_, v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec(v_as_x27_5705_);
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object* v_sz_5712_, lean_object* v_i_5713_, lean_object* v_bs_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_){
_start:
{
size_t v_sz_boxed_5718_; size_t v_i_boxed_5719_; lean_object* v_res_5720_; 
v_sz_boxed_5718_ = lean_unbox_usize(v_sz_5712_);
lean_dec(v_sz_5712_);
v_i_boxed_5719_ = lean_unbox_usize(v_i_5713_);
lean_dec(v_i_5713_);
v_res_5720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_boxed_5718_, v_i_boxed_5719_, v_bs_5714_, v___y_5715_, v___y_5716_);
lean_dec_ref(v___y_5715_);
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_sz_5721_, lean_object* v_i_5722_, lean_object* v_bs_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
size_t v_sz_boxed_5727_; size_t v_i_boxed_5728_; lean_object* v_res_5729_; 
v_sz_boxed_5727_ = lean_unbox_usize(v_sz_5721_);
lean_dec(v_sz_5721_);
v_i_boxed_5728_ = lean_unbox_usize(v_i_5722_);
lean_dec(v_i_5722_);
v_res_5729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__20(v_sz_boxed_5727_, v_i_boxed_5728_, v_bs_5723_, v___y_5724_, v___y_5725_);
lean_dec_ref(v___y_5724_);
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5730_, lean_object* v_val_5731_, lean_object* v_as_x27_5732_, lean_object* v_b_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_){
_start:
{
uint8_t v___x_173356__boxed_5737_; lean_object* v_res_5738_; 
v___x_173356__boxed_5737_ = lean_unbox(v___x_5730_);
v_res_5738_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173356__boxed_5737_, v_val_5731_, v_as_x27_5732_, v_b_5733_, v___y_5734_, v___y_5735_);
lean_dec_ref(v___y_5734_);
lean_dec(v_as_x27_5732_);
lean_dec_ref(v_val_5731_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_){
_start:
{
lean_object* v_res_5743_; 
v_res_5743_ = l_LeanExport_dumpExprAux(v_e_5739_, v_a_5740_, v_a_5741_);
lean_dec_ref(v_a_5740_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_){
_start:
{
lean_object* v_res_5748_; 
v_res_5748_ = l_LeanExport_dumpConstant(v_c_5744_, v_a_5745_, v_a_5746_);
lean_dec_ref(v_a_5745_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5749_, lean_object* v_as_5750_, lean_object* v_as_x27_5751_, lean_object* v_b_5752_, lean_object* v_a_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5749_, v_as_x27_5751_, v_b_5752_, v___y_5754_, v___y_5755_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5758_, lean_object* v_as_5759_, lean_object* v_as_x27_5760_, lean_object* v_b_5761_, lean_object* v_a_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_){
_start:
{
uint8_t v___x_177923__boxed_5766_; lean_object* v_res_5767_; 
v___x_177923__boxed_5766_ = lean_unbox(v___x_5758_);
v_res_5767_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_177923__boxed_5766_, v_as_5759_, v_as_x27_5760_, v_b_5761_, v_a_5762_, v___y_5763_, v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec(v_as_x27_5760_);
lean_dec(v_as_5759_);
return v_res_5767_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5768_, uint8_t v___x_5769_, lean_object* v_as_5770_, lean_object* v_as_x27_5771_, lean_object* v_b_5772_, lean_object* v_a_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
lean_object* v___x_5777_; 
v___x_5777_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5768_, v___x_5769_, v_as_x27_5771_, v_b_5772_, v___y_5774_, v___y_5775_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5778_, lean_object* v___x_5779_, lean_object* v_as_5780_, lean_object* v_as_x27_5781_, lean_object* v_b_5782_, lean_object* v_a_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
uint8_t v___y_177940__boxed_5787_; uint8_t v___x_177941__boxed_5788_; lean_object* v_res_5789_; 
v___y_177940__boxed_5787_ = lean_unbox(v___y_5778_);
v___x_177941__boxed_5788_ = lean_unbox(v___x_5779_);
v_res_5789_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_177940__boxed_5787_, v___x_177941__boxed_5788_, v_as_5780_, v_as_x27_5781_, v_b_5782_, v_a_5783_, v___y_5784_, v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v_as_x27_5781_);
lean_dec(v_as_5780_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5790_, lean_object* v_t_5791_, lean_object* v_k_5792_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5791_, v_k_5792_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_5794_, lean_object* v_t_5795_, lean_object* v_k_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_5794_, v_t_5795_, v_k_5796_);
lean_dec(v_k_5796_);
lean_dec(v_t_5795_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_5798_, lean_object* v_val_5799_, lean_object* v_as_5800_, lean_object* v_as_x27_5801_, lean_object* v_b_5802_, lean_object* v_a_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5798_, v_val_5799_, v_as_x27_5801_, v_b_5802_, v___y_5804_, v___y_5805_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_5808_, lean_object* v_val_5809_, lean_object* v_as_5810_, lean_object* v_as_x27_5811_, lean_object* v_b_5812_, lean_object* v_a_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
uint8_t v___x_177962__boxed_5817_; lean_object* v_res_5818_; 
v___x_177962__boxed_5817_ = lean_unbox(v___x_5808_);
v_res_5818_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_177962__boxed_5817_, v_val_5809_, v_as_5810_, v_as_x27_5811_, v_b_5812_, v_a_5813_, v___y_5814_, v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v_as_x27_5811_);
lean_dec(v_as_5810_);
lean_dec_ref(v_val_5809_);
return v_res_5818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_5819_, lean_object* v_as_x27_5820_, lean_object* v_b_5821_, lean_object* v_a_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v___x_5826_; 
v___x_5826_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5820_, v_b_5821_, v___y_5823_, v___y_5824_);
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_5827_, lean_object* v_as_x27_5828_, lean_object* v_b_5829_, lean_object* v_a_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5827_, v_as_x27_5828_, v_b_5829_, v_a_5830_, v___y_5831_, v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v_as_x27_5828_);
lean_dec(v_as_5827_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_5835_, lean_object* v_as_x27_5836_, lean_object* v_b_5837_, lean_object* v_a_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5836_, v_b_5837_, v___y_5839_, v___y_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_5843_, lean_object* v_as_x27_5844_, lean_object* v_b_5845_, lean_object* v_a_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_){
_start:
{
lean_object* v_res_5850_; 
v_res_5850_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5843_, v_as_x27_5844_, v_b_5845_, v_a_5846_, v___y_5847_, v___y_5848_);
lean_dec_ref(v___y_5847_);
lean_dec(v_as_x27_5844_);
lean_dec(v_as_5843_);
return v_res_5850_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = l_Lean_versionString;
v___x_5853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5852_);
return v___x_5853_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5854_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_5855_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_5856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
lean_ctor_set(v___x_5856_, 1, v___x_5854_);
return v___x_5856_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5858_ = l_Lean_githash;
v___x_5859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
return v___x_5859_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5860_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_5861_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_5862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5861_);
lean_ctor_set(v___x_5862_, 1, v___x_5860_);
return v___x_5862_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5863_ = lean_box(0);
v___x_5864_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_5865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
lean_ctor_set(v___x_5865_, 1, v___x_5863_);
return v___x_5865_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_5867_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_5868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5867_);
lean_ctor_set(v___x_5868_, 1, v___x_5866_);
return v___x_5868_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_5869_; lean_object* v_leanMeta_5870_; 
v___x_5869_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_5870_ = l_Lean_Json_mkObj(v___x_5869_);
return v_leanMeta_5870_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_5889_; lean_object* v_exporterMeta_5890_; 
v___x_5889_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_5890_ = l_Lean_Json_mkObj(v___x_5889_);
return v_exporterMeta_5890_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_5891_; lean_object* v_formatMeta_5892_; 
v___x_5891_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_5892_ = l_Lean_Json_mkObj(v___x_5891_);
return v_formatMeta_5892_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v_exporterMeta_5895_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_5896_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_5897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5896_);
lean_ctor_set(v___x_5897_, 1, v_exporterMeta_5895_);
return v___x_5897_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; 
v_leanMeta_5899_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_5900_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5900_);
lean_ctor_set(v___x_5901_, 1, v_leanMeta_5899_);
return v___x_5901_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v_formatMeta_5903_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_5904_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_5905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
lean_ctor_set(v___x_5905_, 1, v_formatMeta_5903_);
return v___x_5905_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_5908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5907_);
lean_ctor_set(v___x_5908_, 1, v___x_5906_);
return v___x_5908_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5909_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_5910_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_5911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
lean_ctor_set(v___x_5911_, 1, v___x_5909_);
return v___x_5911_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5912_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_5913_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_5914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
lean_ctor_set(v___x_5914_, 1, v___x_5912_);
return v___x_5914_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5915_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_5916_ = l_Lean_Json_mkObj(v___x_5915_);
return v___x_5916_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5917_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_5918_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
lean_ctor_set(v___x_5919_, 1, v___x_5917_);
return v___x_5919_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5920_ = lean_box(0);
v___x_5921_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_5922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
lean_ctor_set(v___x_5922_, 1, v___x_5920_);
return v___x_5922_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; 
v___x_5923_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_5924_ = l_Lean_Json_mkObj(v___x_5923_);
return v___x_5924_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_5925_; 
v___x_5925_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_5925_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
v___x_5926_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_5927_ = l_Lean_Json_compress(v___x_5926_);
return v___x_5927_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_5928_){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5930_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_5931_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_5930_);
if (lean_obj_tag(v___x_5931_) == 0)
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5940_; 
v_a_5932_ = lean_ctor_get(v___x_5931_, 0);
v_isSharedCheck_5940_ = !lean_is_exclusive(v___x_5931_);
if (v_isSharedCheck_5940_ == 0)
{
v___x_5934_ = v___x_5931_;
v_isShared_5935_ = v_isSharedCheck_5940_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5931_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5940_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5936_; lean_object* v___x_5938_; 
v___x_5936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5936_, 0, v_a_5932_);
lean_ctor_set(v___x_5936_, 1, v_a_5928_);
if (v_isShared_5935_ == 0)
{
lean_ctor_set(v___x_5934_, 0, v___x_5936_);
v___x_5938_ = v___x_5934_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v___x_5936_);
v___x_5938_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
return v___x_5938_;
}
}
}
else
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5948_; 
lean_dec_ref(v_a_5928_);
v_a_5941_ = lean_ctor_get(v___x_5931_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v___x_5931_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5943_ = v___x_5931_;
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5931_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5946_; 
if (v_isShared_5944_ == 0)
{
v___x_5946_ = v___x_5943_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_5949_, lean_object* v_a_5950_){
_start:
{
lean_object* v_res_5951_; 
v_res_5951_ = l_LeanExport_dumpMetadata___redArg(v_a_5949_);
return v_res_5951_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_5952_, lean_object* v_a_5953_){
_start:
{
lean_object* v___x_5955_; 
v___x_5955_ = l_LeanExport_dumpMetadata___redArg(v_a_5953_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l_LeanExport_dumpMetadata(v_a_5956_, v_a_5957_);
lean_dec_ref(v_a_5956_);
return v_res_5959_;
}
}
lean_object* runtime_initialize_Lean(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_LeanExport_Basic_0__LeanExport_exportMetadata = _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata();
lean_mark_persistent(l___private_LeanExport_Basic_0__LeanExport_exportMetadata);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanExport_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

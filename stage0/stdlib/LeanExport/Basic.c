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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_Lean_versionString;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_println___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--export-unsafe"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanExport.dumpConstant"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "assertion violation: ((!ctorVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1873.0 ).exportUnsafe)\n          "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a `ConstantInfo.ctorInfo`."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "assertion violation: ((!recVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.2114.0 ).exportUnsafe)\n        "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "expected a `constantinfo.recinfo`."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value;
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value)}};
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_nbuckets_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_173_ = lean_array_get_size(v_data_172_);
v___x_174_ = lean_unsigned_to_nat(2u);
v_nbuckets_175_ = lean_nat_mul(v___x_173_, v___x_174_);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_box(0);
v___x_178_ = lean_mk_array(v_nbuckets_175_, v___x_177_);
v___x_179_ = lean_array_propagate_mark(v_data_172_, v___x_178_);
v___x_180_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v___x_176_, v_data_172_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
else
{
lean_object* v_key_184_; lean_object* v_tail_185_; uint8_t v___x_186_; 
v_key_184_ = lean_ctor_get(v_x_182_, 0);
v_tail_185_ = lean_ctor_get(v_x_182_, 2);
v___x_186_ = lean_name_eq(v_key_184_, v_a_181_);
if (v___x_186_ == 0)
{
v_x_182_ = v_tail_185_;
goto _start;
}
else
{
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_188_, v_x_189_);
lean_dec(v_x_189_);
lean_dec(v_a_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object* v_m_192_, lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
lean_object* v_size_195_; lean_object* v_buckets_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_242_; 
v_size_195_ = lean_ctor_get(v_m_192_, 0);
v_buckets_196_ = lean_ctor_get(v_m_192_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_m_192_);
if (v_isSharedCheck_242_ == 0)
{
v___x_198_ = v_m_192_;
v_isShared_199_ = v_isSharedCheck_242_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_buckets_196_);
lean_inc(v_size_195_);
lean_dec(v_m_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_242_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; uint64_t v___y_202_; 
v___x_200_ = lean_array_get_size(v_buckets_196_);
if (lean_obj_tag(v_a_193_) == 0)
{
uint64_t v___x_240_; 
v___x_240_ = 1723ULL;
v___y_202_ = v___x_240_;
goto v___jp_201_;
}
else
{
uint64_t v_hash_241_; 
v_hash_241_ = lean_ctor_get_uint64(v_a_193_, sizeof(void*)*2);
v___y_202_ = v_hash_241_;
goto v___jp_201_;
}
v___jp_201_:
{
uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v_fold_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_bkt_214_; uint8_t v___x_215_; 
v___x_203_ = 32ULL;
v___x_204_ = lean_uint64_shift_right(v___y_202_, v___x_203_);
v_fold_205_ = lean_uint64_xor(v___y_202_, v___x_204_);
v___x_206_ = 16ULL;
v___x_207_ = lean_uint64_shift_right(v_fold_205_, v___x_206_);
v___x_208_ = lean_uint64_xor(v_fold_205_, v___x_207_);
v___x_209_ = lean_uint64_to_usize(v___x_208_);
v___x_210_ = lean_usize_of_nat(v___x_200_);
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_sub(v___x_210_, v___x_211_);
v___x_213_ = lean_usize_land(v___x_209_, v___x_212_);
v_bkt_214_ = lean_array_uget_borrowed(v_buckets_196_, v___x_213_);
v___x_215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_193_, v_bkt_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v_size_x27_217_; lean_object* v___x_218_; lean_object* v_buckets_x27_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v_size_x27_217_ = lean_nat_add(v_size_195_, v___x_216_);
lean_dec(v_size_195_);
lean_inc(v_bkt_214_);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v_a_193_);
lean_ctor_set(v___x_218_, 1, v_b_194_);
lean_ctor_set(v___x_218_, 2, v_bkt_214_);
v_buckets_x27_219_ = lean_array_uset(v_buckets_196_, v___x_213_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(4u);
v___x_221_ = lean_nat_mul(v_size_x27_217_, v___x_220_);
v___x_222_ = lean_unsigned_to_nat(3u);
v___x_223_ = lean_nat_div(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_array_get_size(v_buckets_x27_219_);
v___x_225_ = lean_nat_dec_le(v___x_223_, v___x_224_);
lean_dec(v___x_223_);
if (v___x_225_ == 0)
{
lean_object* v_val_226_; lean_object* v___x_228_; 
v_val_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_buckets_x27_219_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_val_226_);
lean_ctor_set(v___x_198_, 0, v_size_x27_217_);
v___x_228_ = v___x_198_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_buckets_x27_219_);
lean_ctor_set(v___x_198_, 0, v_size_x27_217_);
v___x_231_ = v___x_198_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_buckets_x27_219_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v___x_233_; lean_object* v_buckets_x27_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_inc(v_bkt_214_);
v___x_233_ = lean_box(0);
v_buckets_x27_234_ = lean_array_uset(v_buckets_196_, v___x_213_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_193_, v_b_194_, v_bkt_214_);
v___x_236_ = lean_array_uset(v_buckets_x27_234_, v___x_213_, v___x_235_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_236_);
v___x_238_ = v___x_198_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_195_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object* v_a_243_, lean_object* v_b_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_dec(v_b_244_);
lean_dec(v_a_243_);
return v_x_245_;
}
else
{
lean_object* v_key_246_; lean_object* v_value_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v_key_246_ = lean_ctor_get(v_x_245_, 0);
v_value_247_ = lean_ctor_get(v_x_245_, 1);
v_tail_248_ = lean_ctor_get(v_x_245_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v_x_245_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_value_247_);
lean_inc(v_key_246_);
lean_dec(v_x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_level_eq(v_key_246_, v_a_243_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_243_, v_b_244_, v_tail_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 2, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_key_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_value_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v_value_247_);
lean_dec(v_key_246_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_b_244_);
lean_ctor_set(v___x_250_, 0, v_a_243_);
v___x_258_ = v___x_250_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_243_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_b_244_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_tail_248_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
return v_x_261_;
}
else
{
lean_object* v_key_263_; lean_object* v_value_264_; lean_object* v_tail_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_288_; 
v_key_263_ = lean_ctor_get(v_x_262_, 0);
v_value_264_ = lean_ctor_get(v_x_262_, 1);
v_tail_265_ = lean_ctor_get(v_x_262_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_288_ == 0)
{
v___x_267_ = v_x_262_;
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_tail_265_);
lean_inc(v_value_264_);
lean_inc(v_key_263_);
lean_dec(v_x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v_fold_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_269_ = lean_array_get_size(v_x_261_);
v___x_270_ = l_Lean_Level_hash(v_key_263_);
v___x_271_ = 32ULL;
v___x_272_ = lean_uint64_shift_right(v___x_270_, v___x_271_);
v_fold_273_ = lean_uint64_xor(v___x_270_, v___x_272_);
v___x_274_ = 16ULL;
v___x_275_ = lean_uint64_shift_right(v_fold_273_, v___x_274_);
v___x_276_ = lean_uint64_xor(v_fold_273_, v___x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = lean_usize_of_nat(v___x_269_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_sub(v___x_278_, v___x_279_);
v___x_281_ = lean_usize_land(v___x_277_, v___x_280_);
v___x_282_ = lean_array_uget_borrowed(v_x_261_, v___x_281_);
lean_inc(v___x_282_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 2, v___x_282_);
v___x_284_ = v___x_267_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_key_263_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_value_264_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v___x_282_);
v___x_284_ = v_reuseFailAlloc_287_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_uset(v_x_261_, v___x_281_, v___x_284_);
v_x_261_ = v___x_285_;
v_x_262_ = v_tail_265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object* v_i_289_, lean_object* v_source_290_, lean_object* v_target_291_){
_start:
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_array_get_size(v_source_290_);
v___x_293_ = lean_nat_dec_lt(v_i_289_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec_ref(v_source_290_);
lean_dec(v_i_289_);
return v_target_291_;
}
else
{
lean_object* v_es_294_; lean_object* v___x_295_; lean_object* v_source_296_; lean_object* v_target_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_es_294_ = lean_array_fget(v_source_290_, v_i_289_);
v___x_295_ = lean_box(0);
v_source_296_ = lean_array_fset(v_source_290_, v_i_289_, v___x_295_);
v_target_297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_target_291_, v_es_294_);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_289_, v___x_298_);
lean_dec(v_i_289_);
v_i_289_ = v___x_299_;
v_source_290_ = v_source_296_;
v_target_291_ = v_target_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object* v_data_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_nbuckets_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_302_ = lean_array_get_size(v_data_301_);
v___x_303_ = lean_unsigned_to_nat(2u);
v_nbuckets_304_ = lean_nat_mul(v___x_302_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_box(0);
v___x_307_ = lean_mk_array(v_nbuckets_304_, v___x_306_);
v___x_308_ = lean_array_propagate_mark(v_data_301_, v___x_307_);
v___x_309_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v___x_305_, v_data_301_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object* v_a_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
else
{
lean_object* v_key_313_; lean_object* v_tail_314_; uint8_t v___x_315_; 
v_key_313_ = lean_ctor_get(v_x_311_, 0);
v_tail_314_ = lean_ctor_get(v_x_311_, 2);
v___x_315_ = lean_level_eq(v_key_313_, v_a_310_);
if (v___x_315_ == 0)
{
v_x_311_ = v_tail_314_;
goto _start;
}
else
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_317_, v_x_318_);
lean_dec(v_x_318_);
lean_dec(v_a_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_368_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_368_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_368_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_bkt_342_; uint8_t v___x_343_; 
v___x_329_ = lean_array_get_size(v_buckets_325_);
v___x_330_ = l_Lean_Level_hash(v_a_322_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v_bkt_342_ = lean_array_uget_borrowed(v_buckets_325_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_322_, v_bkt_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v_size_x27_345_; lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v_size_x27_345_ = lean_nat_add(v_size_324_, v___x_344_);
lean_dec(v_size_324_);
lean_inc(v_bkt_342_);
v___x_346_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_346_, 0, v_a_322_);
lean_ctor_set(v___x_346_, 1, v_b_323_);
lean_ctor_set(v___x_346_, 2, v_bkt_342_);
v_buckets_x27_347_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_nat_mul(v_size_x27_345_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(3u);
v___x_351_ = lean_nat_div(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_array_get_size(v_buckets_x27_347_);
v___x_353_ = lean_nat_dec_le(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
if (v___x_353_ == 0)
{
lean_object* v_val_354_; lean_object* v___x_356_; 
v_val_354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_buckets_x27_347_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_354_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_356_ = v___x_327_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_val_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_object* v___x_359_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_347_);
lean_ctor_set(v___x_327_, 0, v_size_x27_345_);
v___x_359_ = v___x_327_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_size_x27_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_buckets_x27_347_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v_buckets_x27_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_bkt_342_);
v___x_361_ = lean_box(0);
v_buckets_x27_362_ = lean_array_uset(v_buckets_325_, v___x_341_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_322_, v_b_323_, v_bkt_342_);
v___x_364_ = lean_array_uset(v_buckets_x27_362_, v___x_341_, v___x_363_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_364_);
v___x_366_ = v___x_327_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_unsigned_to_nat(524288u);
v___x_371_ = lean_mk_array(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__0, &l_LeanExport_M_run___redArg___closed__0_once, _init_l_LeanExport_M_run___redArg___closed__0);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_box(0);
v___x_377_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__1, &l_LeanExport_M_run___redArg___closed__1_once, _init_l_LeanExport_M_run___redArg___closed__1);
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v___x_377_, v___x_376_, v___x_375_);
return v___x_378_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_unsigned_to_nat(2048u);
v___x_381_ = lean_mk_array(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__3, &l_LeanExport_M_run___redArg___closed__3_once, _init_l_LeanExport_M_run___redArg___closed__3);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_box(0);
v___x_387_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__4, &l_LeanExport_M_run___redArg___closed__4_once, _init_l_LeanExport_M_run___redArg___closed__4);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v___x_387_, v___x_386_, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__6(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
v___x_390_ = lean_unsigned_to_nat(16777216u);
v___x_391_ = lean_mk_array(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__6, &l_LeanExport_M_run___redArg___closed__6_once, _init_l_LeanExport_M_run___redArg___closed__6);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_unsigned_to_nat(16u);
v___x_397_ = lean_mk_array(v___x_396_, v___x_395_);
return v___x_397_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__8, &l_LeanExport_M_run___redArg___closed__8_once, _init_l_LeanExport_M_run___redArg___closed__8);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__10(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_box(0);
v___x_402_ = lean_unsigned_to_nat(262144u);
v___x_403_ = lean_mk_array(v___x_402_, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__11(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__10, &l_LeanExport_M_run___redArg___closed__10_once, _init_l_LeanExport_M_run___redArg___closed__10);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
return v___x_406_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__12(void){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_407_ = lean_box(1);
v___x_408_ = 0;
v___x_409_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__11, &l_LeanExport_M_run___redArg___closed__11_once, _init_l_LeanExport_M_run___redArg___closed__11);
v___x_410_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__9, &l_LeanExport_M_run___redArg___closed__9_once, _init_l_LeanExport_M_run___redArg___closed__9);
v___x_411_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__7, &l_LeanExport_M_run___redArg___closed__7_once, _init_l_LeanExport_M_run___redArg___closed__7);
v___x_412_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__5, &l_LeanExport_M_run___redArg___closed__5_once, _init_l_LeanExport_M_run___redArg___closed__5);
v___x_413_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__2, &l_LeanExport_M_run___redArg___closed__2_once, _init_l_LeanExport_M_run___redArg___closed__2);
v___x_414_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
lean_ctor_set(v___x_414_, 3, v___x_410_);
lean_ctor_set(v___x_414_, 4, v___x_409_);
lean_ctor_set(v___x_414_, 5, v___x_407_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6, v___x_408_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6 + 1, v___x_408_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*6 + 2, v___x_408_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object* v_env_415_, lean_object* v_act_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__12, &l_LeanExport_M_run___redArg___closed__12_once, _init_l_LeanExport_M_run___redArg___closed__12);
v___x_419_ = lean_apply_3(v_act_416_, v_env_415_, v___x_418_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_fst_424_; lean_object* v___x_426_; 
v_fst_424_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_fst_424_);
lean_dec(v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_fst_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_419_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object* v_env_437_, lean_object* v_act_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_LeanExport_M_run___redArg(v_env_437_, v_act_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object* v_00_u03b1_441_, lean_object* v_env_442_, lean_object* v_act_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_LeanExport_M_run___redArg(v_env_442_, v_act_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object* v_00_u03b1_446_, lean_object* v_env_447_, lean_object* v_act_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_LeanExport_M_run(v_00_u03b1_446_, v_env_447_, v_act_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_m_452_, v_a_453_, v_b_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object* v_00_u03b2_456_, lean_object* v_m_457_, lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_m_457_, v_a_458_, v_b_459_);
return v___x_460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(v_00_u03b2_465_, v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_data_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_data_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_474_, v_b_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object* v_00_u03b2_478_, lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object* v_00_u03b2_482_, lean_object* v_a_483_, lean_object* v_x_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(v_00_u03b2_482_, v_a_483_, v_x_484_);
lean_dec(v_x_484_);
lean_dec(v_a_483_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_data_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_data_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_a_491_, lean_object* v_b_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_491_, v_b_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_495_, lean_object* v_i_496_, lean_object* v_source_497_, lean_object* v_target_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v_i_496_, v_source_497_, v_target_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_500_, lean_object* v_i_501_, lean_object* v_source_502_, lean_object* v_target_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v_i_501_, v_source_502_, v_target_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_x_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_x_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object* v_val_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_toConstantVal_515_; lean_object* v_name_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_toConstantVal_515_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_toConstantVal_515_);
lean_dec_ref(v_val_513_);
v_name_516_ = lean_ctor_get(v_toConstantVal_515_, 0);
lean_inc(v_name_516_);
lean_dec_ref(v_toConstantVal_515_);
v___x_517_ = l_Lean_NameSet_empty;
v___x_518_ = l_Lean_NameSet_insert(v___x_517_, v_name_516_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_toConstantVal_520_; lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_530_; 
v_toConstantVal_520_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_toConstantVal_520_);
lean_dec_ref(v_val_513_);
v_val_521_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_523_ = v_x_514_;
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v_x_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_name_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v_name_525_ = lean_ctor_get(v_toConstantVal_520_, 0);
lean_inc(v_name_525_);
lean_dec_ref(v_toConstantVal_520_);
v___x_526_ = l_Lean_NameSet_insert(v_val_521_, v_name_525_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_526_);
v___x_528_ = v___x_523_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object* v_val_531_, lean_object* v_k_532_, lean_object* v_t_533_){
_start:
{
if (lean_obj_tag(v_t_533_) == 0)
{
lean_object* v_size_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_553_; 
v_size_534_ = lean_ctor_get(v_t_533_, 0);
v_k_535_ = lean_ctor_get(v_t_533_, 1);
v_v_536_ = lean_ctor_get(v_t_533_, 2);
v_l_537_ = lean_ctor_get(v_t_533_, 3);
v_r_538_ = lean_ctor_get(v_t_533_, 4);
v_isSharedCheck_553_ = !lean_is_exclusive(v_t_533_);
if (v_isSharedCheck_553_ == 0)
{
v___x_540_ = v_t_533_;
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_r_538_);
lean_inc(v_l_537_);
lean_inc(v_v_536_);
lean_inc(v_k_535_);
lean_inc(v_size_534_);
lean_dec(v_t_533_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_553_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___x_542_; 
v___x_542_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_532_, v_k_535_);
switch(v___x_542_)
{
case 0:
{
lean_object* v_impl_543_; lean_object* v___x_544_; 
lean_del_object(v___x_540_);
lean_dec(v_size_534_);
v_impl_543_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_531_, v_k_532_, v_l_537_);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_535_, v_v_536_, v_impl_543_, v_r_538_);
return v___x_544_;
}
case 1:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_val_547_; lean_object* v___x_549_; 
lean_dec(v_k_535_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_v_536_);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_531_, v___x_545_);
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec(v___x_546_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 2, v_val_547_);
lean_ctor_set(v___x_540_, 1, v_k_532_);
v___x_549_ = v___x_540_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_size_534_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_k_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_val_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_l_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_r_538_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
default: 
{
lean_object* v_impl_551_; lean_object* v___x_552_; 
lean_del_object(v___x_540_);
lean_dec(v_size_534_);
v_impl_551_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_531_, v_k_532_, v_r_538_);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_535_, v_v_536_, v_l_537_, v_impl_551_);
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_val_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_554_ = lean_box(0);
v___x_555_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_531_, v___x_554_);
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec(v___x_555_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_k_532_);
lean_ctor_set(v___x_558_, 2, v_val_556_);
lean_ctor_set(v___x_558_, 3, v_t_533_);
lean_ctor_set(v___x_558_, 4, v_t_533_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object* v_val_559_, lean_object* v_as_x27_560_, lean_object* v_b_561_, lean_object* v___y_562_){
_start:
{
if (lean_obj_tag(v_as_x27_560_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_val_559_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_b_561_);
lean_ctor_set(v___x_564_, 1, v___y_562_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
else
{
lean_object* v_head_566_; lean_object* v_tail_567_; lean_object* v___x_568_; 
v_head_566_ = lean_ctor_get(v_as_x27_560_, 0);
v_tail_567_ = lean_ctor_get(v_as_x27_560_, 1);
lean_inc(v_head_566_);
lean_inc_ref(v_val_559_);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_559_, v_head_566_, v_b_561_);
v_as_x27_560_ = v_tail_567_;
v_b_561_ = v___x_568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object* v_val_570_, lean_object* v_as_x27_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_570_, v_as_x27_571_, v_b_572_, v___y_573_);
lean_dec(v_as_x27_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object* v_x_576_, lean_object* v_y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_a_583_; lean_object* v_snd_584_; 
if (lean_obj_tag(v_y_577_) == 7)
{
lean_object* v_val_590_; lean_object* v_all_591_; lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; 
v_val_590_ = lean_ctor_get(v_y_577_, 0);
lean_inc_ref(v_val_590_);
lean_dec_ref_known(v_y_577_, 1);
v_all_591_ = lean_ctor_get(v_val_590_, 1);
lean_inc(v_all_591_);
v___x_592_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_590_, v_all_591_, v___y_578_, v___y_580_);
lean_dec(v_all_591_);
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v_fst_594_ = lean_ctor_get(v_a_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v_a_593_, 1);
lean_inc(v_snd_595_);
lean_dec(v_a_593_);
v_a_583_ = v_fst_594_;
v_snd_584_ = v_snd_595_;
goto v___jp_582_;
}
else
{
lean_dec_ref(v_y_577_);
v_a_583_ = v___y_578_;
v_snd_584_ = v___y_580_;
goto v___jp_582_;
}
v___jp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_a_583_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_snd_584_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object* v_x_596_, lean_object* v_y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_LeanExport_initState___lam__0(v_x_596_, v_y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v_x_596_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_604_) == 0)
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
else
{
lean_object* v_head_606_; lean_object* v_tail_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_head_606_ = lean_ctor_get(v_x_604_, 0);
v_tail_607_ = lean_ctor_get(v_x_604_, 1);
v___x_608_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__2___closed__0));
v___x_609_ = lean_string_dec_eq(v_head_606_, v___x_608_);
if (v___x_609_ == 0)
{
v_x_604_ = v_tail_607_;
goto _start;
}
else
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object* v_x_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_List_any___at___00LeanExport_initState_spec__2(v_x_611_);
lean_dec(v_x_611_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
else
{
lean_object* v_head_617_; lean_object* v_tail_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_head_617_ = lean_ctor_get(v_x_615_, 0);
v_tail_618_ = lean_ctor_get(v_x_615_, 1);
v___x_619_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__0___closed__0));
v___x_620_ = lean_string_dec_eq(v_head_617_, v___x_619_);
if (v___x_620_ == 0)
{
v_x_615_ = v_tail_618_;
goto _start;
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_List_any___at___00LeanExport_initState_spec__0(v_x_622_);
lean_dec(v_x_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_f_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_f_625_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_x_626_);
lean_ctor_set(v___x_632_, 1, v___y_628_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___y_630_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_key_636_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_key_636_);
v_value_637_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_value_637_);
v_tail_638_ = lean_ctor_get(v_x_627_, 2);
lean_inc(v_tail_638_);
lean_dec_ref_known(v_x_627_, 3);
lean_inc_ref(v_f_625_);
lean_inc_ref(v___y_629_);
v___x_639_ = lean_apply_6(v_f_625_, v_key_636_, v_value_637_, v___y_628_, v___y_629_, v___y_630_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_fst_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
v_fst_641_ = lean_ctor_get(v_a_640_, 0);
if (lean_obj_tag(v_fst_641_) == 0)
{
lean_dec(v_a_640_);
lean_dec(v_tail_638_);
lean_dec_ref(v_f_625_);
return v___x_639_;
}
else
{
lean_object* v_a_642_; lean_object* v_snd_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; 
lean_dec_ref_known(v___x_639_, 1);
v_a_642_ = lean_ctor_get(v_fst_641_, 0);
lean_inc(v_a_642_);
v_snd_643_ = lean_ctor_get(v_a_640_, 1);
lean_inc(v_snd_643_);
lean_dec(v_a_640_);
v_fst_644_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_645_);
lean_dec(v_a_642_);
v_x_626_ = v_fst_644_;
v_x_627_ = v_tail_638_;
v___y_628_ = v_snd_645_;
v___y_630_ = v_snd_643_;
goto _start;
}
}
else
{
lean_dec(v_tail_638_);
lean_dec_ref(v_f_625_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_f_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_647_, v_x_648_, v_x_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object* v_f_655_, lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v___x_666_ = lean_box(0);
lean_inc(v___x_665_);
lean_inc_ref(v_f_655_);
v___x_667_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_655_, v___x_666_, v___x_665_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_fst_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
v_fst_669_ = lean_ctor_get(v_a_668_, 0);
if (lean_obj_tag(v_fst_669_) == 0)
{
lean_dec(v_a_668_);
lean_dec_ref(v_f_655_);
return v___x_667_;
}
else
{
lean_object* v_a_670_; lean_object* v_snd_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; size_t v___x_674_; size_t v___x_675_; 
lean_dec_ref_known(v___x_667_, 1);
v_a_670_ = lean_ctor_get(v_fst_669_, 0);
lean_inc(v_a_670_);
v_snd_671_ = lean_ctor_get(v_a_668_, 1);
lean_inc(v_snd_671_);
lean_dec(v_a_668_);
v_fst_672_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_672_);
v_snd_673_ = lean_ctor_get(v_a_670_, 1);
lean_inc(v_snd_673_);
lean_dec(v_a_670_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_657_, v___x_674_);
v_i_657_ = v___x_675_;
v_b_659_ = v_fst_672_;
v___y_660_ = v_snd_673_;
v___y_662_ = v_snd_671_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_655_);
return v___x_667_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec_ref(v_f_655_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_b_659_);
lean_ctor_set(v___x_677_, 1, v___y_660_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___y_662_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object* v_f_681_, lean_object* v_as_682_, lean_object* v_i_683_, lean_object* v_stop_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
size_t v_i_boxed_690_; size_t v_stop_boxed_691_; lean_object* v_res_692_; 
v_i_boxed_690_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_stop_boxed_691_ = lean_unbox_usize(v_stop_684_);
lean_dec(v_stop_684_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_681_, v_as_682_, v_i_boxed_690_, v_stop_boxed_691_, v_b_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v_as_682_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
lean_inc_ref(v___y_698_);
v___x_701_ = lean_apply_6(v_f_693_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object* v_f_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_i_714_, lean_object* v_acc_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_keys_712_);
v___x_721_ = lean_nat_dec_lt(v_i_714_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_acc_715_);
lean_ctor_set(v___x_722_, 1, v___y_716_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___y_718_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v_k_726_; lean_object* v_v_727_; lean_object* v___x_728_; 
v_k_726_ = lean_array_fget_borrowed(v_keys_712_, v_i_714_);
v_v_727_ = lean_array_fget_borrowed(v_vals_713_, v_i_714_);
lean_inc_ref(v_f_711_);
lean_inc_ref(v___y_717_);
lean_inc(v_v_727_);
lean_inc(v_k_726_);
v___x_728_ = lean_apply_7(v_f_711_, v_acc_715_, v_k_726_, v_v_727_, v___y_716_, v___y_717_, v___y_718_, lean_box(0));
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v_fst_730_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
v_fst_730_ = lean_ctor_get(v_a_729_, 0);
if (lean_obj_tag(v_fst_730_) == 0)
{
lean_dec(v_a_729_);
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
return v___x_728_;
}
else
{
lean_object* v_a_731_; lean_object* v_snd_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref_known(v___x_728_, 1);
v_a_731_ = lean_ctor_get(v_fst_730_, 0);
lean_inc(v_a_731_);
v_snd_732_ = lean_ctor_get(v_a_729_, 1);
lean_inc(v_snd_732_);
lean_dec(v_a_729_);
v_fst_733_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_fst_733_);
v_snd_734_ = lean_ctor_get(v_a_731_, 1);
lean_inc(v_snd_734_);
lean_dec(v_a_731_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_i_714_, v___x_735_);
lean_dec(v_i_714_);
v_i_714_ = v___x_736_;
v_acc_715_ = v_fst_733_;
v___y_716_ = v_snd_734_;
v___y_718_ = v_snd_732_;
goto _start;
}
}
else
{
lean_dec(v_i_714_);
lean_dec_ref(v_f_711_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_f_738_, lean_object* v_keys_739_, lean_object* v_vals_740_, lean_object* v_i_741_, lean_object* v_acc_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_738_, v_keys_739_, v_vals_740_, v_i_741_, v_acc_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec_ref(v_vals_740_);
lean_dec_ref(v_keys_739_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_f_748_, lean_object* v_as_749_, size_t v_i_750_, size_t v_stop_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v_snd_760_; lean_object* v___y_765_; uint8_t v___x_772_; 
v___x_772_ = lean_usize_dec_eq(v_i_750_, v_stop_751_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
v___x_773_ = lean_array_uget_borrowed(v_as_749_, v_i_750_);
switch(lean_obj_tag(v___x_773_))
{
case 0:
{
lean_object* v_key_774_; lean_object* v_val_775_; lean_object* v___x_776_; 
v_key_774_ = lean_ctor_get(v___x_773_, 0);
v_val_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_f_748_);
lean_inc_ref(v___y_754_);
lean_inc(v_val_775_);
lean_inc(v_key_774_);
v___x_776_ = lean_apply_7(v_f_748_, v_b_752_, v_key_774_, v_val_775_, v___y_753_, v___y_754_, v___y_755_, lean_box(0));
v___y_765_ = v___x_776_;
goto v___jp_764_;
}
case 1:
{
lean_object* v_node_777_; lean_object* v___x_778_; 
v_node_777_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_node_777_);
lean_inc_ref(v_f_748_);
v___x_778_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_748_, v_node_777_, v_b_752_, v___y_753_, v___y_754_, v___y_755_);
v___y_765_ = v___x_778_;
goto v___jp_764_;
}
default: 
{
v_fst_758_ = v_b_752_;
v_snd_759_ = v___y_753_;
v_snd_760_ = v___y_755_;
goto v___jp_757_;
}
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_f_748_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_b_752_);
lean_ctor_set(v___x_779_, 1, v___y_753_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___y_755_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
v___jp_757_:
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_750_, v___x_761_);
v_i_750_ = v___x_762_;
v_b_752_ = v_fst_758_;
v___y_753_ = v_snd_759_;
v___y_755_ = v_snd_760_;
goto _start;
}
v___jp_764_:
{
if (lean_obj_tag(v___y_765_) == 0)
{
lean_object* v_a_766_; lean_object* v_fst_767_; 
v_a_766_ = lean_ctor_get(v___y_765_, 0);
v_fst_767_ = lean_ctor_get(v_a_766_, 0);
if (lean_obj_tag(v_fst_767_) == 0)
{
lean_dec_ref(v_f_748_);
return v___y_765_;
}
else
{
lean_object* v_a_768_; lean_object* v_snd_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; 
lean_inc(v_a_766_);
lean_dec_ref_known(v___y_765_, 1);
v_a_768_ = lean_ctor_get(v_fst_767_, 0);
lean_inc(v_a_768_);
v_snd_769_ = lean_ctor_get(v_a_766_, 1);
lean_inc(v_snd_769_);
lean_dec(v_a_766_);
v_fst_770_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_fst_770_);
v_snd_771_ = lean_ctor_get(v_a_768_, 1);
lean_inc(v_snd_771_);
lean_dec(v_a_768_);
v_fst_758_ = v_fst_770_;
v_snd_759_ = v_snd_771_;
v_snd_760_ = v_snd_769_;
goto v___jp_757_;
}
}
else
{
lean_dec_ref(v_f_748_);
return v___y_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_f_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_es_790_ = lean_ctor_get(v_x_784_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v_x_784_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_es_790_);
lean_dec(v_x_784_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_es_790_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_799_; 
lean_dec_ref(v_es_790_);
lean_dec_ref(v_f_783_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_x_785_);
lean_ctor_set(v___x_797_, 1, v___y_786_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___y_788_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
lean_del_object(v___x_792_);
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_795_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_783_, v_es_790_, v___x_803_, v___x_804_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v_es_790_);
return v___x_805_;
}
}
}
else
{
lean_object* v_ks_807_; lean_object* v_vs_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_ks_807_ = lean_ctor_get(v_x_784_, 0);
lean_inc_ref(v_ks_807_);
v_vs_808_ = lean_ctor_get(v_x_784_, 1);
lean_inc_ref(v_vs_808_);
lean_dec_ref_known(v_x_784_, 2);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_783_, v_ks_807_, v_vs_808_, v___x_809_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v_vs_808_);
lean_dec_ref(v_ks_807_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_f_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_811_, v_x_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_f_819_, lean_object* v_as_820_, lean_object* v_i_821_, lean_object* v_stop_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
size_t v_i_boxed_828_; size_t v_stop_boxed_829_; lean_object* v_res_830_; 
v_i_boxed_828_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_stop_boxed_829_ = lean_unbox_usize(v_stop_822_);
lean_dec(v_stop_822_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_819_, v_as_820_, v_i_boxed_828_, v_stop_boxed_829_, v_b_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v_as_820_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_831_, lean_object* v_f_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___f_837_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_837_, 0, v_f_832_);
v___x_838_ = lean_box(0);
v___x_839_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v___f_837_, v_map_831_, v___x_838_, v___y_833_, v___y_834_, v___y_835_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_840_, lean_object* v_f_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_840_, v_f_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object* v_s_847_, lean_object* v_f_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_map_u2081_853_; lean_object* v_map_u2082_854_; lean_object* v_buckets_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_map_u2081_853_ = lean_ctor_get(v_s_847_, 0);
lean_inc_ref(v_map_u2081_853_);
v_map_u2082_854_ = lean_ctor_get(v_s_847_, 1);
lean_inc_ref(v_map_u2082_854_);
lean_dec_ref(v_s_847_);
v_buckets_855_ = lean_ctor_get(v_map_u2081_853_, 1);
lean_inc_ref(v_buckets_855_);
lean_dec_ref(v_map_u2081_853_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v_buckets_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_dec_ref(v_buckets_855_);
v___x_859_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_854_, v_f_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_860_ = lean_box(0);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_857_);
lean_inc_ref(v_f_848_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_848_, v_buckets_855_, v___x_861_, v___x_862_, v___x_860_, v___y_849_, v___y_850_, v___y_851_);
lean_dec_ref(v_buckets_855_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v_fst_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
v_fst_865_ = lean_ctor_get(v_a_864_, 0);
if (lean_obj_tag(v_fst_865_) == 0)
{
lean_dec(v_a_864_);
lean_dec_ref(v_map_u2082_854_);
lean_dec_ref(v_f_848_);
return v___x_863_;
}
else
{
lean_object* v_a_866_; lean_object* v_snd_867_; lean_object* v_snd_868_; lean_object* v___x_869_; 
lean_dec_ref_known(v___x_863_, 1);
v_a_866_ = lean_ctor_get(v_fst_865_, 0);
lean_inc(v_a_866_);
v_snd_867_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_snd_867_);
lean_dec(v_a_864_);
v_snd_868_ = lean_ctor_get(v_a_866_, 1);
lean_inc(v_snd_868_);
lean_dec(v_a_866_);
v___x_869_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_854_, v_f_848_, v_snd_868_, v___y_850_, v_snd_867_);
return v___x_869_;
}
}
else
{
lean_dec_ref(v_map_u2082_854_);
lean_dec_ref(v_f_848_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object* v_s_870_, lean_object* v_f_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_870_, v_f_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 0;
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_head_880_ = lean_ctor_get(v_x_878_, 0);
v_tail_881_ = lean_ctor_get(v_x_878_, 1);
v___x_882_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_883_ = lean_string_dec_eq(v_head_880_, v___x_882_);
if (v___x_883_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_885_);
lean_dec(v_x_885_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object* v_env_889_, lean_object* v_cliOptions_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___f_916_; lean_object* v_recursorMap_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___f_916_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_917_ = lean_box(1);
v___x_918_ = l_Lean_Environment_constants(v_env_889_);
v___x_919_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v___x_918_, v___f_916_, v_recursorMap_917_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v_fst_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v_fst_921_ = lean_ctor_get(v_a_920_, 0);
if (lean_obj_tag(v_fst_921_) == 0)
{
lean_object* v_snd_922_; lean_object* v_a_923_; 
lean_inc_ref(v_fst_921_);
v_snd_922_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_922_);
lean_dec(v_a_920_);
v_a_923_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v_fst_921_, 1);
v_fst_895_ = v_a_923_;
v_snd_896_ = v_snd_922_;
goto v___jp_894_;
}
else
{
lean_object* v_a_924_; lean_object* v_snd_925_; lean_object* v_snd_926_; 
v_a_924_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_a_924_);
v_snd_925_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_snd_925_);
lean_dec(v_a_920_);
v_snd_926_ = lean_ctor_get(v_a_924_, 1);
lean_inc(v_snd_926_);
lean_dec(v_a_924_);
v_fst_895_ = v_snd_926_;
v_snd_896_ = v_snd_925_;
goto v___jp_894_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_919_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_919_);
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
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_894_:
{
lean_object* v_visitedNames_897_; lean_object* v_visitedLevels_898_; lean_object* v_visitedExprs_899_; lean_object* v_visitedConstants_900_; lean_object* v_noMDataExprs_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_914_; 
v_visitedNames_897_ = lean_ctor_get(v_snd_896_, 0);
v_visitedLevels_898_ = lean_ctor_get(v_snd_896_, 1);
v_visitedExprs_899_ = lean_ctor_get(v_snd_896_, 2);
v_visitedConstants_900_ = lean_ctor_get(v_snd_896_, 3);
v_noMDataExprs_901_ = lean_ctor_get(v_snd_896_, 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v_snd_896_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_snd_896_, 5);
lean_dec(v_unused_915_);
v___x_903_ = v_snd_896_;
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_noMDataExprs_901_);
lean_inc(v_visitedConstants_900_);
lean_inc(v_visitedExprs_899_);
lean_inc(v_visitedLevels_898_);
lean_inc(v_visitedNames_897_);
lean_dec(v_snd_896_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_914_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; uint8_t v___x_906_; uint8_t v___x_907_; uint8_t v___x_908_; lean_object* v___x_910_; 
v___x_905_ = lean_box(0);
v___x_906_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_890_);
v___x_907_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_890_);
v___x_908_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_890_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 5, v_fst_895_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_visitedNames_897_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_visitedLevels_898_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_visitedExprs_899_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_visitedConstants_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_noMDataExprs_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 5, v_fst_895_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6, v___x_906_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6 + 1, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*6 + 2, v___x_908_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_905_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_935_, lean_object* v_cliOptions_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_LeanExport_initState(v_env_935_, v_cliOptions_936_, v_a_937_, v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_cliOptions_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_941_, lean_object* v_k_942_, lean_object* v_t_943_, lean_object* v_hl_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_941_, v_k_942_, v_t_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_946_, lean_object* v_as_947_, lean_object* v_as_x27_948_, lean_object* v_b_949_, lean_object* v_a_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_946_, v_as_x27_948_, v_b_949_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_955_, lean_object* v_as_956_, lean_object* v_as_x27_957_, lean_object* v_b_958_, lean_object* v_a_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_955_, v_as_956_, v_as_x27_957_, v_b_958_, v_a_959_, v___y_960_, v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v_as_x27_957_);
lean_dec(v_as_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_00_u03b2_964_, lean_object* v_s_965_, lean_object* v_f_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_965_, v_f_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_00_u03b2_972_, lean_object* v_s_973_, lean_object* v_f_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(v_00_u03b2_972_, v_s_973_, v_f_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b2_980_, lean_object* v_f_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_981_, v_x_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b2_989_, lean_object* v_f_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b2_989_, v_f_990_, v_x_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_998_, lean_object* v_map_999_, lean_object* v_f_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_999_, v_f_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_map_1007_, lean_object* v_f_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1006_, v_map_1007_, v_f_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object* v_00_u03b2_1014_, lean_object* v_f_1015_, lean_object* v_as_1016_, size_t v_i_1017_, size_t v_stop_1018_, lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_1015_, v_as_1016_, v_i_1017_, v_stop_1018_, v_b_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_f_1026_, lean_object* v_as_1027_, lean_object* v_i_1028_, lean_object* v_stop_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_i_boxed_1035_; size_t v_stop_boxed_1036_; lean_object* v_res_1037_; 
v_i_boxed_1035_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_stop_boxed_1036_ = lean_unbox_usize(v_stop_1029_);
lean_dec(v_stop_1029_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(v_00_u03b2_1025_, v_f_1026_, v_as_1027_, v_i_boxed_1035_, v_stop_boxed_1036_, v_b_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1027_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object* v_map_1038_, lean_object* v_f_1039_, lean_object* v_init_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1039_, v_map_1038_, v_init_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_map_1046_, lean_object* v_f_1047_, lean_object* v_init_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1046_, v_f_1047_, v_init_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object* v_00_u03c3_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_map_1056_, lean_object* v_f_1057_, lean_object* v_init_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1057_, v_map_1056_, v_init_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03c3_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_map_1066_, lean_object* v_f_1067_, lean_object* v_init_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(v_00_u03c3_1064_, v_00_u03b2_1065_, v_map_1066_, v_f_1067_, v_init_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03c3_1074_, lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_f_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1077_, v_x_1078_, v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03c3_1085_, lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_f_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(v_00_u03c3_1085_, v_00_u03b1_1086_, v_00_u03b2_1087_, v_f_1088_, v_x_1089_, v_x_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_00_u03c3_1098_, lean_object* v_f_1099_, lean_object* v_as_1100_, size_t v_i_1101_, size_t v_stop_1102_, lean_object* v_b_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_1099_, v_as_1100_, v_i_1101_, v_stop_1102_, v_b_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_00_u03c3_1111_, lean_object* v_f_1112_, lean_object* v_as_1113_, lean_object* v_i_1114_, lean_object* v_stop_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
size_t v_i_boxed_1121_; size_t v_stop_boxed_1122_; lean_object* v_res_1123_; 
v_i_boxed_1121_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_stop_boxed_1122_ = lean_unbox_usize(v_stop_1115_);
lean_dec(v_stop_1115_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_1109_, v_00_u03b2_1110_, v_00_u03c3_1111_, v_f_1112_, v_as_1113_, v_i_boxed_1121_, v_stop_boxed_1122_, v_b_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1113_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_f_1127_, lean_object* v_keys_1128_, lean_object* v_vals_1129_, lean_object* v_heq_1130_, lean_object* v_i_1131_, lean_object* v_acc_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_1127_, v_keys_1128_, v_vals_1129_, v_i_1131_, v_acc_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03c3_1138_, lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_f_1141_, lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_heq_1144_, lean_object* v_i_1145_, lean_object* v_acc_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(v_00_u03c3_1138_, v_00_u03b1_1139_, v_00_u03b2_1140_, v_f_1141_, v_keys_1142_, v_vals_1143_, v_heq_1144_, v_i_1145_, v_acc_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec_ref(v_vals_1143_);
lean_dec_ref(v_keys_1142_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_x_1155_, lean_object* v_namespaced_1156_, lean_object* v_getM_1157_, lean_object* v_setM_1158_, lean_object* v_rec_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_inc_ref(v_getM_1157_);
lean_inc_ref(v_a_1161_);
v___x_1163_ = lean_apply_1(v_getM_1157_, v_a_1161_);
lean_inc(v_x_1155_);
lean_inc_ref(v_inst_1153_);
lean_inc_ref(v_inst_1154_);
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1154_, v_inst_1153_, v___x_1163_, v_x_1155_);
lean_dec_ref(v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_rec_1159_);
lean_dec_ref(v_setM_1158_);
lean_dec_ref(v_getM_1157_);
lean_dec_ref(v_namespaced_1156_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_val_1165_);
lean_ctor_set(v___x_1169_, 1, v_a_1161_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_dec(v___x_1164_);
v___f_1174_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1160_);
v___x_1175_ = lean_apply_3(v_rec_1159_, v_a_1160_, v_a_1161_, lean_box(0));
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1210_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v_fst_1177_ = lean_ctor_get(v_a_1176_, 0);
v_snd_1178_ = lean_ctor_get(v_a_1176_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1176_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1180_ = v_a_1176_;
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_a_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1210_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v_size_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_inc(v_snd_1178_);
v___x_1182_ = lean_apply_1(v_getM_1157_, v_snd_1178_);
v_size_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_n(v_size_1183_, 2);
v___x_1184_ = l_Lean_JsonNumber_fromNat(v_size_1183_);
v___x_1185_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
v___x_1186_ = l_Lean_Json_setObjVal_x21(v_fst_1177_, v_namespaced_1156_, v___x_1185_);
v___x_1187_ = l_Lean_Json_compress(v___x_1186_);
v___x_1188_ = l_IO_println___redArg(v___f_1174_, v___x_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1200_; 
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1201_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_inc(v_size_1183_);
v___x_1192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1154_, v_inst_1153_, v___x_1182_, v_x_1155_, v_size_1183_);
v___x_1193_ = lean_apply_2(v_setM_1158_, v_snd_1178_, v___x_1192_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1193_);
lean_ctor_set(v___x_1180_, 0, v_size_1183_);
v___x_1195_ = v___x_1180_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_1183_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1195_);
v___x_1197_ = v___x_1190_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_size_1183_);
lean_dec_ref(v___x_1182_);
lean_del_object(v___x_1180_);
lean_dec(v_snd_1178_);
lean_dec_ref(v_setM_1158_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_a_1202_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1188_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1188_);
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
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_setM_1158_);
lean_dec_ref(v_getM_1157_);
lean_dec_ref(v_namespaced_1156_);
lean_dec(v_x_1155_);
lean_dec_ref(v_inst_1154_);
lean_dec_ref(v_inst_1153_);
v_a_1211_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1175_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1175_);
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
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_x_1221_, lean_object* v_namespaced_1222_, lean_object* v_getM_1223_, lean_object* v_setM_1224_, lean_object* v_rec_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1219_, v_inst_1220_, v_x_1221_, v_namespaced_1222_, v_getM_1223_, v_setM_1224_, v_rec_1225_, v_a_1226_, v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_x_1233_, lean_object* v_namespaced_1234_, lean_object* v_getM_1235_, lean_object* v_setM_1236_, lean_object* v_rec_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_inc_ref(v_getM_1235_);
lean_inc_ref(v_a_1239_);
v___x_1241_ = lean_apply_1(v_getM_1235_, v_a_1239_);
lean_inc(v_x_1233_);
lean_inc_ref(v_inst_1231_);
lean_inc_ref(v_inst_1232_);
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1232_, v_inst_1231_, v___x_1241_, v_x_1233_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_rec_1237_);
lean_dec_ref(v_setM_1236_);
lean_dec_ref(v_getM_1235_);
lean_dec_ref(v_namespaced_1234_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_val_1243_);
lean_ctor_set(v___x_1247_, 1, v_a_1239_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___f_1252_; lean_object* v___x_1253_; 
lean_dec(v___x_1242_);
v___f_1252_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1238_);
v___x_1253_ = lean_apply_3(v_rec_1237_, v_a_1238_, v_a_1239_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_fst_1255_; lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1288_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_fst_1255_ = lean_ctor_get(v_a_1254_, 0);
v_snd_1256_ = lean_ctor_get(v_a_1254_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1258_ = v_a_1254_;
v_isShared_1259_ = v_isSharedCheck_1288_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_inc(v_fst_1255_);
lean_dec(v_a_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1288_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v_size_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc(v_snd_1256_);
v___x_1260_ = lean_apply_1(v_getM_1235_, v_snd_1256_);
v_size_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_n(v_size_1261_, 2);
v___x_1262_ = l_Lean_JsonNumber_fromNat(v_size_1261_);
v___x_1263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
v___x_1264_ = l_Lean_Json_setObjVal_x21(v_fst_1255_, v_namespaced_1234_, v___x_1263_);
v___x_1265_ = l_Lean_Json_compress(v___x_1264_);
v___x_1266_ = l_IO_println___redArg(v___f_1252_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1279_);
v___x_1268_ = v___x_1266_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v___x_1266_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_inc(v_size_1261_);
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1232_, v_inst_1231_, v___x_1260_, v_x_1233_, v_size_1261_);
v___x_1271_ = lean_apply_2(v_setM_1236_, v_snd_1256_, v___x_1270_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1271_);
lean_ctor_set(v___x_1258_, 0, v_size_1261_);
v___x_1273_ = v___x_1258_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_size_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1273_);
v___x_1275_ = v___x_1268_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_size_1261_);
lean_dec_ref(v___x_1260_);
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_dec_ref(v_setM_1236_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_a_1280_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1266_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1266_);
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
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_setM_1236_);
lean_dec_ref(v_getM_1235_);
lean_dec_ref(v_namespaced_1234_);
lean_dec(v_x_1233_);
lean_dec_ref(v_inst_1232_);
lean_dec_ref(v_inst_1231_);
v_a_1289_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1253_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1253_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
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
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_x_1300_, lean_object* v_namespaced_1301_, lean_object* v_getM_1302_, lean_object* v_setM_1303_, lean_object* v_rec_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1297_, v_inst_1298_, v_inst_1299_, v_x_1300_, v_namespaced_1301_, v_getM_1302_, v_setM_1303_, v_rec_1304_, v_a_1305_, v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1308_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_instMonadEIO___redArg();
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___f_1327_; lean_object* v___x_1421__overap_1328_; lean_object* v___x_1329_; 
v___x_1314_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1315_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1315_, 0, v___x_1314_);
v___f_1316_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1316_, 0, v___x_1314_);
v___f_1317_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1317_, 0, v___x_1314_);
v___f_1318_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1318_, 0, v___x_1314_);
v___x_1319_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1319_, 0, lean_box(0));
lean_closure_set(v___x_1319_, 1, lean_box(0));
lean_closure_set(v___x_1319_, 2, v___x_1314_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___f_1315_);
v___x_1321_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v___x_1314_);
v___x_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_ctor_set(v___x_1322_, 2, v___f_1316_);
lean_ctor_set(v___x_1322_, 3, v___f_1317_);
lean_ctor_set(v___x_1322_, 4, v___f_1318_);
v___x_1323_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, lean_box(0));
lean_closure_set(v___x_1323_, 2, v___x_1314_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_box(0);
v___x_1326_ = l_instInhabitedOfMonad___redArg(v___x_1324_, v___x_1325_);
v___f_1327_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1327_, 0, v___x_1326_);
v___x_1421__overap_1328_ = lean_panic_fn_borrowed(v___f_1327_, v_msg_1310_);
lean_dec_ref(v___f_1327_);
lean_inc_ref(v___y_1311_);
v___x_1329_ = lean_apply_3(v___x_1421__overap_1328_, v___y_1311_, v___y_1312_, lean_box(0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1330_, v___y_1331_, v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v_key_1338_; lean_object* v_value_1339_; lean_object* v_tail_1340_; uint8_t v___x_1341_; 
v_key_1338_ = lean_ctor_get(v_x_1336_, 0);
v_value_1339_ = lean_ctor_get(v_x_1336_, 1);
v_tail_1340_ = lean_ctor_get(v_x_1336_, 2);
v___x_1341_ = lean_name_eq(v_key_1338_, v_a_1335_);
if (v___x_1341_ == 0)
{
v_x_1336_ = v_tail_1340_;
goto _start;
}
else
{
lean_object* v___x_1343_; 
lean_inc(v_value_1339_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_value_1339_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1344_, v_x_1345_);
lean_dec(v_x_1345_);
lean_dec(v_a_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_buckets_1349_; lean_object* v___x_1350_; uint64_t v___y_1352_; 
v_buckets_1349_ = lean_ctor_get(v_m_1347_, 1);
v___x_1350_ = lean_array_get_size(v_buckets_1349_);
if (lean_obj_tag(v_a_1348_) == 0)
{
uint64_t v___x_1366_; 
v___x_1366_ = 1723ULL;
v___y_1352_ = v___x_1366_;
goto v___jp_1351_;
}
else
{
uint64_t v_hash_1367_; 
v_hash_1367_ = lean_ctor_get_uint64(v_a_1348_, sizeof(void*)*2);
v___y_1352_ = v_hash_1367_;
goto v___jp_1351_;
}
v___jp_1351_:
{
uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v_fold_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1353_ = 32ULL;
v___x_1354_ = lean_uint64_shift_right(v___y_1352_, v___x_1353_);
v_fold_1355_ = lean_uint64_xor(v___y_1352_, v___x_1354_);
v___x_1356_ = 16ULL;
v___x_1357_ = lean_uint64_shift_right(v_fold_1355_, v___x_1356_);
v___x_1358_ = lean_uint64_xor(v_fold_1355_, v___x_1357_);
v___x_1359_ = lean_uint64_to_usize(v___x_1358_);
v___x_1360_ = lean_usize_of_nat(v___x_1350_);
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_sub(v___x_1360_, v___x_1361_);
v___x_1363_ = lean_usize_land(v___x_1359_, v___x_1362_);
v___x_1364_ = lean_array_uget_borrowed(v_buckets_1349_, v___x_1363_);
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1348_, v___x_1364_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_m_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v_putStr_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_get_stdout();
v_putStr_1374_ = lean_ctor_get(v___x_1373_, 4);
lean_inc_ref(v_putStr_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = lean_apply_2(v_putStr_1374_, v_s_1371_, lean_box(0));
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1379_){
_start:
{
uint32_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = 10;
v___x_1382_ = lean_string_push(v_s_1379_, v___x_1381_);
v___x_1383_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1384_);
return v_res_1386_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1392_ = lean_unsigned_to_nat(18u);
v___x_1393_ = lean_unsigned_to_nat(114u);
v___x_1394_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1395_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1396_ = l_mkPanicMessageWithDecl(v___x_1395_, v___x_1394_, v___x_1393_, v___x_1392_, v___x_1391_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_visitedNames_1405_; lean_object* v___x_1406_; 
v_visitedNames_1405_ = lean_ctor_get(v_a_1403_, 0);
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1405_, v_n_1401_);
if (lean_obj_tag(v___x_1406_) == 1)
{
lean_object* v_val_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_n_1401_);
v_val_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_val_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_val_1407_);
lean_ctor_set(v___x_1411_, 1, v_a_1403_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v___x_1416_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; 
lean_dec(v___x_1406_);
v___x_1416_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1401_))
{
case 0:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1461_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1460_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_fst_1463_; lean_object* v_snd_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v_fst_1463_ = lean_ctor_get(v_a_1462_, 0);
lean_inc(v_fst_1463_);
v_snd_1464_ = lean_ctor_get(v_a_1462_, 1);
lean_inc(v_snd_1464_);
lean_dec(v_a_1462_);
v_fst_1418_ = v_fst_1463_;
v_snd_1419_ = v_snd_1464_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1461_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1461_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
case 1:
{
lean_object* v_pre_1473_; lean_object* v_str_1474_; lean_object* v___x_1475_; 
v_pre_1473_ = lean_ctor_get(v_n_1401_, 0);
v_str_1474_ = lean_ctor_get(v_n_1401_, 1);
lean_inc(v_pre_1473_);
v___x_1475_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1473_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1504_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1504_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1504_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1503_; 
v_fst_1480_ = lean_ctor_get(v_a_1476_, 0);
v_snd_1481_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1483_ = v_a_1476_;
v_isShared_1484_ = v_isSharedCheck_1503_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_inc(v_fst_1480_);
lean_dec(v_a_1476_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1503_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1485_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1486_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1487_ = l_Lean_JsonNumber_fromNat(v_fst_1480_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 2);
lean_ctor_set(v___x_1478_, 0, v___x_1487_);
v___x_1489_ = v___x_1478_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1489_);
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1491_ = v___x_1483_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v_str_1474_);
v___x_1492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_str_1474_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1485_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1491_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_Json_mkObj(v___x_1496_);
lean_dec_ref_known(v___x_1496_, 2);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1485_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1494_);
v___x_1500_ = l_Lean_Json_mkObj(v___x_1499_);
lean_dec_ref_known(v___x_1499_, 2);
v_fst_1418_ = v___x_1500_;
v_snd_1419_ = v_snd_1481_;
goto v___jp_1417_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1401_, 2);
return v___x_1475_;
}
}
default: 
{
lean_object* v_pre_1505_; lean_object* v_i_1506_; lean_object* v___x_1507_; 
v_pre_1505_ = lean_ctor_get(v_n_1401_, 0);
v_i_1506_ = lean_ctor_get(v_n_1401_, 1);
lean_inc(v_pre_1505_);
v___x_1507_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1505_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1538_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1538_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1538_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1537_; 
v_fst_1512_ = lean_ctor_get(v_a_1508_, 0);
v_snd_1513_ = lean_ctor_get(v_a_1508_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1515_ = v_a_1508_;
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snd_1513_);
lean_inc(v_fst_1512_);
lean_dec(v_a_1508_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1537_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1517_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1518_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1519_ = l_Lean_JsonNumber_fromNat(v_fst_1512_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 2);
lean_ctor_set(v___x_1510_, 0, v___x_1519_);
v___x_1521_ = v___x_1510_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1521_);
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1523_ = v___x_1515_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1524_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1506_);
v___x_1525_ = l_Lean_JsonNumber_fromNat(v_i_1506_);
v___x_1526_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1524_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1523_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Lean_Json_mkObj(v___x_1530_);
lean_dec_ref_known(v___x_1530_, 2);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1517_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1528_);
v___x_1534_ = l_Lean_Json_mkObj(v___x_1533_);
lean_dec_ref_known(v___x_1533_, 2);
v_fst_1418_ = v___x_1534_;
v_snd_1419_ = v_snd_1513_;
goto v___jp_1417_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1401_, 2);
return v___x_1507_;
}
}
}
v___jp_1417_:
{
lean_object* v_visitedNames_1420_; lean_object* v_visitedLevels_1421_; lean_object* v_visitedExprs_1422_; lean_object* v_visitedConstants_1423_; lean_object* v_noMDataExprs_1424_; uint8_t v_exportMData_1425_; uint8_t v_exportUnsafe_1426_; uint8_t v_ignoreMissing_1427_; lean_object* v_recursorMap_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1459_; 
v_visitedNames_1420_ = lean_ctor_get(v_snd_1419_, 0);
v_visitedLevels_1421_ = lean_ctor_get(v_snd_1419_, 1);
v_visitedExprs_1422_ = lean_ctor_get(v_snd_1419_, 2);
v_visitedConstants_1423_ = lean_ctor_get(v_snd_1419_, 3);
v_noMDataExprs_1424_ = lean_ctor_get(v_snd_1419_, 4);
v_exportMData_1425_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6);
v_exportUnsafe_1426_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6 + 1);
v_ignoreMissing_1427_ = lean_ctor_get_uint8(v_snd_1419_, sizeof(void*)*6 + 2);
v_recursorMap_1428_ = lean_ctor_get(v_snd_1419_, 5);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_snd_1419_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1430_ = v_snd_1419_;
v_isShared_1431_ = v_isSharedCheck_1459_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_recursorMap_1428_);
lean_inc(v_noMDataExprs_1424_);
lean_inc(v_visitedConstants_1423_);
lean_inc(v_visitedExprs_1422_);
lean_inc(v_visitedLevels_1421_);
lean_inc(v_visitedNames_1420_);
lean_dec(v_snd_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1459_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_size_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_size_1432_ = lean_ctor_get(v_visitedNames_1420_, 0);
lean_inc_n(v_size_1432_, 2);
v___x_1433_ = l_Lean_JsonNumber_fromNat(v_size_1432_);
v___x_1434_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
v___x_1435_ = l_Lean_Json_setObjVal_x21(v_fst_1418_, v___x_1416_, v___x_1434_);
v___x_1436_ = l_Lean_Json_compress(v___x_1435_);
v___x_1437_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1437_, 0);
lean_dec(v_unused_1450_);
v___x_1439_ = v___x_1437_;
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v___x_1437_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1449_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_inc(v_size_1432_);
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1420_, v_n_1401_, v_size_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1441_);
v___x_1443_ = v___x_1430_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_visitedLevels_1421_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_visitedExprs_1422_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_visitedConstants_1423_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_noMDataExprs_1424_);
lean_ctor_set(v_reuseFailAlloc_1448_, 5, v_recursorMap_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6, v_exportMData_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6 + 1, v_exportUnsafe_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*6 + 2, v_ignoreMissing_1427_);
v___x_1443_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_size_1432_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_size_1432_);
lean_del_object(v___x_1430_);
lean_dec(v_recursorMap_1428_);
lean_dec_ref(v_noMDataExprs_1424_);
lean_dec_ref(v_visitedConstants_1423_);
lean_dec_ref(v_visitedExprs_1422_);
lean_dec_ref(v_visitedLevels_1421_);
lean_dec_ref(v_visitedNames_1420_);
lean_dec(v_n_1401_);
v_a_1451_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1437_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1437_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1539_, v_a_1540_, v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1544_, lean_object* v_m_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1545_, v_a_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1548_, v_m_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_m_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1552_, lean_object* v_a_1553_, lean_object* v_x_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1553_, v_x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1556_, lean_object* v_a_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1556_, v_a_1557_, v_x_1558_);
lean_dec(v_x_1558_);
lean_dec(v_a_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1560_, lean_object* v_x_1561_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
else
{
lean_object* v_key_1563_; lean_object* v_value_1564_; lean_object* v_tail_1565_; uint8_t v___x_1566_; 
v_key_1563_ = lean_ctor_get(v_x_1561_, 0);
v_value_1564_ = lean_ctor_get(v_x_1561_, 1);
v_tail_1565_ = lean_ctor_get(v_x_1561_, 2);
v___x_1566_ = lean_level_eq(v_key_1563_, v_a_1560_);
if (v___x_1566_ == 0)
{
v_x_1561_ = v_tail_1565_;
goto _start;
}
else
{
lean_object* v___x_1568_; 
lean_inc(v_value_1564_);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_value_1564_);
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1569_, v_x_1570_);
lean_dec(v_x_1570_);
lean_dec(v_a_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_buckets_1574_; lean_object* v___x_1575_; uint64_t v___x_1576_; uint64_t v___x_1577_; uint64_t v___x_1578_; uint64_t v_fold_1579_; uint64_t v___x_1580_; uint64_t v___x_1581_; uint64_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_buckets_1574_ = lean_ctor_get(v_m_1572_, 1);
v___x_1575_ = lean_array_get_size(v_buckets_1574_);
v___x_1576_ = l_Lean_Level_hash(v_a_1573_);
v___x_1577_ = 32ULL;
v___x_1578_ = lean_uint64_shift_right(v___x_1576_, v___x_1577_);
v_fold_1579_ = lean_uint64_xor(v___x_1576_, v___x_1578_);
v___x_1580_ = 16ULL;
v___x_1581_ = lean_uint64_shift_right(v_fold_1579_, v___x_1580_);
v___x_1582_ = lean_uint64_xor(v_fold_1579_, v___x_1581_);
v___x_1583_ = lean_uint64_to_usize(v___x_1582_);
v___x_1584_ = lean_usize_of_nat(v___x_1575_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_sub(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_usize_land(v___x_1583_, v___x_1586_);
v___x_1588_ = lean_array_uget_borrowed(v_buckets_1574_, v___x_1587_);
v___x_1589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1573_, v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_m_1590_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1600_ = lean_unsigned_to_nat(23u);
v___x_1601_ = lean_unsigned_to_nat(132u);
v___x_1602_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1603_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1603_, v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_visitedLevels_1609_; lean_object* v___x_1610_; 
v_visitedLevels_1609_ = lean_ctor_get(v_a_1607_, 1);
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1609_, v_l_1605_);
if (lean_obj_tag(v___x_1610_) == 1)
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_l_1605_);
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_val_1611_);
lean_ctor_set(v___x_1615_, 1, v_a_1607_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
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
lean_object* v___x_1620_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; 
lean_dec(v___x_1610_);
v___x_1620_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1605_))
{
case 1:
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v_l_1605_, 0);
lean_inc(v_a_1664_);
v___x_1665_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1664_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1687_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1687_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1687_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_fst_1670_; lean_object* v_snd_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1686_; 
v_fst_1670_ = lean_ctor_get(v_a_1666_, 0);
v_snd_1671_ = lean_ctor_get(v_a_1666_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_a_1666_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1673_ = v_a_1666_;
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_snd_1671_);
lean_inc(v_fst_1670_);
lean_dec(v_a_1666_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1686_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1676_ = l_Lean_JsonNumber_fromNat(v_fst_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 2);
lean_ctor_set(v___x_1668_, 0, v___x_1676_);
v___x_1678_ = v___x_1668_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1678_);
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1680_ = v___x_1673_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_Json_mkObj(v___x_1682_);
lean_dec_ref_known(v___x_1682_, 2);
v_fst_1622_ = v___x_1683_;
v_snd_1623_ = v_snd_1671_;
goto v___jp_1621_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 1);
return v___x_1665_;
}
}
case 2:
{
lean_object* v_a_1688_; lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1688_ = lean_ctor_get(v_l_1605_, 0);
v_a_1689_ = lean_ctor_get(v_l_1605_, 1);
lean_inc(v_a_1688_);
v___x_1690_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1688_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1735_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1734_; 
v_fst_1695_ = lean_ctor_get(v_a_1691_, 0);
v_snd_1696_ = lean_ctor_get(v_a_1691_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1698_ = v_a_1691_;
v_isShared_1699_ = v_isSharedCheck_1734_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snd_1696_);
lean_inc(v_fst_1695_);
lean_dec(v_a_1691_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1734_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; 
lean_inc(v_a_1689_);
v___x_1700_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1689_, v_a_1606_, v_snd_1696_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1733_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1733_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1733_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1732_; 
v_fst_1705_ = lean_ctor_get(v_a_1701_, 0);
v_snd_1706_ = lean_ctor_get(v_a_1701_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1708_ = v_a_1701_;
v_isShared_1709_ = v_isSharedCheck_1732_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_a_1701_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1732_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1711_ = l_Lean_JsonNumber_fromNat(v_fst_1695_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 2);
lean_ctor_set(v___x_1703_, 0, v___x_1711_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = l_Lean_JsonNumber_fromNat(v_fst_1705_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 2);
lean_ctor_set(v___x_1693_, 0, v___x_1714_);
v___x_1716_ = v___x_1693_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1717_ = lean_unsigned_to_nat(2u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_array_push(v___x_1718_, v___x_1713_);
v___x_1720_ = lean_array_push(v___x_1719_, v___x_1716_);
v___x_1721_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___x_1721_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1723_ = v___x_1708_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 1);
lean_ctor_set(v___x_1698_, 1, v___x_1724_);
lean_ctor_set(v___x_1698_, 0, v___x_1723_);
v___x_1726_ = v___x_1698_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Json_mkObj(v___x_1726_);
lean_dec_ref(v___x_1726_);
v_fst_1622_ = v___x_1727_;
v_snd_1623_ = v_snd_1706_;
goto v___jp_1621_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1698_);
lean_dec(v_fst_1695_);
lean_del_object(v___x_1693_);
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1700_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1690_;
}
}
case 3:
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v_l_1605_, 0);
v_a_1737_ = lean_ctor_get(v_l_1605_, 1);
lean_inc(v_a_1736_);
v___x_1738_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1736_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1783_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1783_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_fst_1743_; lean_object* v_snd_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1782_; 
v_fst_1743_ = lean_ctor_get(v_a_1739_, 0);
v_snd_1744_ = lean_ctor_get(v_a_1739_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_a_1739_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1746_ = v_a_1739_;
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_snd_1744_);
lean_inc(v_fst_1743_);
lean_dec(v_a_1739_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; 
lean_inc(v_a_1737_);
v___x_1748_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1737_, v_a_1606_, v_snd_1744_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1781_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1781_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1781_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1780_; 
v_fst_1753_ = lean_ctor_get(v_a_1749_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1749_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1749_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1756_ = v_a_1749_;
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1749_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1758_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_1759_ = l_Lean_JsonNumber_fromNat(v_fst_1743_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 2);
lean_ctor_set(v___x_1751_, 0, v___x_1759_);
v___x_1761_ = v___x_1751_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = l_Lean_JsonNumber_fromNat(v_fst_1753_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 2);
lean_ctor_set(v___x_1741_, 0, v___x_1762_);
v___x_1764_ = v___x_1741_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1765_ = lean_unsigned_to_nat(2u);
v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
v___x_1767_ = lean_array_push(v___x_1766_, v___x_1761_);
v___x_1768_ = lean_array_push(v___x_1767_, v___x_1764_);
v___x_1769_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1769_);
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1771_ = v___x_1756_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_box(0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 1);
lean_ctor_set(v___x_1746_, 1, v___x_1772_);
lean_ctor_set(v___x_1746_, 0, v___x_1771_);
v___x_1774_ = v___x_1746_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Json_mkObj(v___x_1774_);
lean_dec_ref(v___x_1774_);
v_fst_1622_ = v___x_1775_;
v_snd_1623_ = v_snd_1754_;
goto v___jp_1621_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1746_);
lean_dec(v_fst_1743_);
lean_del_object(v___x_1741_);
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1748_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 2);
return v___x_1738_;
}
}
case 4:
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v_l_1605_, 0);
lean_inc(v_a_1784_);
v___x_1785_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_1784_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1807_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1807_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1806_; 
v_fst_1790_ = lean_ctor_get(v_a_1786_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1786_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1786_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1793_ = v_a_1786_;
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1786_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1806_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1795_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_1796_ = l_Lean_JsonNumber_fromNat(v_fst_1790_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 2);
lean_ctor_set(v___x_1788_, 0, v___x_1796_);
v___x_1798_ = v___x_1788_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1798_);
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = l_Lean_Json_mkObj(v___x_1802_);
lean_dec_ref_known(v___x_1802_, 2);
v_fst_1622_ = v___x_1803_;
v_snd_1623_ = v_snd_1791_;
goto v___jp_1621_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1605_, 1);
return v___x_1785_;
}
}
default: 
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_1809_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1808_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v_fst_1811_; lean_object* v_snd_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v_fst_1811_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_fst_1811_);
v_snd_1812_ = lean_ctor_get(v_a_1810_, 1);
lean_inc(v_snd_1812_);
lean_dec(v_a_1810_);
v_fst_1622_ = v_fst_1811_;
v_snd_1623_ = v_snd_1812_;
goto v___jp_1621_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_l_1605_);
v_a_1813_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1809_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
v___jp_1621_:
{
lean_object* v_visitedLevels_1624_; lean_object* v_visitedNames_1625_; lean_object* v_visitedExprs_1626_; lean_object* v_visitedConstants_1627_; lean_object* v_noMDataExprs_1628_; uint8_t v_exportMData_1629_; uint8_t v_exportUnsafe_1630_; uint8_t v_ignoreMissing_1631_; lean_object* v_recursorMap_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1663_; 
v_visitedLevels_1624_ = lean_ctor_get(v_snd_1623_, 1);
v_visitedNames_1625_ = lean_ctor_get(v_snd_1623_, 0);
v_visitedExprs_1626_ = lean_ctor_get(v_snd_1623_, 2);
v_visitedConstants_1627_ = lean_ctor_get(v_snd_1623_, 3);
v_noMDataExprs_1628_ = lean_ctor_get(v_snd_1623_, 4);
v_exportMData_1629_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6);
v_exportUnsafe_1630_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6 + 1);
v_ignoreMissing_1631_ = lean_ctor_get_uint8(v_snd_1623_, sizeof(void*)*6 + 2);
v_recursorMap_1632_ = lean_ctor_get(v_snd_1623_, 5);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_snd_1623_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1634_ = v_snd_1623_;
v_isShared_1635_ = v_isSharedCheck_1663_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_recursorMap_1632_);
lean_inc(v_noMDataExprs_1628_);
lean_inc(v_visitedConstants_1627_);
lean_inc(v_visitedExprs_1626_);
lean_inc(v_visitedLevels_1624_);
lean_inc(v_visitedNames_1625_);
lean_dec(v_snd_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1663_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_size_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_size_1636_ = lean_ctor_get(v_visitedLevels_1624_, 0);
lean_inc_n(v_size_1636_, 2);
v___x_1637_ = l_Lean_JsonNumber_fromNat(v_size_1636_);
v___x_1638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___x_1639_ = l_Lean_Json_setObjVal_x21(v_fst_1622_, v___x_1620_, v___x_1638_);
v___x_1640_ = l_Lean_Json_compress(v___x_1639_);
v___x_1641_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1653_; 
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v___x_1641_, 0);
lean_dec(v_unused_1654_);
v___x_1643_ = v___x_1641_;
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v___x_1641_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1653_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_inc(v_size_1636_);
v___x_1645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1624_, v_l_1605_, v_size_1636_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v___x_1645_);
v___x_1647_ = v___x_1634_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_visitedNames_1625_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_visitedExprs_1626_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_visitedConstants_1627_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_noMDataExprs_1628_);
lean_ctor_set(v_reuseFailAlloc_1652_, 5, v_recursorMap_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6, v_exportMData_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6 + 1, v_exportUnsafe_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1652_, sizeof(void*)*6 + 2, v_ignoreMissing_1631_);
v___x_1647_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_size_1636_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1648_);
v___x_1650_ = v___x_1643_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_size_1636_);
lean_del_object(v___x_1634_);
lean_dec(v_recursorMap_1632_);
lean_dec_ref(v_noMDataExprs_1628_);
lean_dec_ref(v_visitedConstants_1627_);
lean_dec_ref(v_visitedExprs_1626_);
lean_dec_ref(v_visitedNames_1625_);
lean_dec_ref(v_visitedLevels_1624_);
lean_dec(v_l_1605_);
v_a_1655_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1641_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1641_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1821_, v_a_1822_, v_a_1823_);
lean_dec_ref(v_a_1822_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_1826_, lean_object* v_m_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1827_, v_a_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_1830_, lean_object* v_m_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_1830_, v_m_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_m_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_1834_, lean_object* v_a_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1838_, lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_1838_, v_a_1839_, v_x_1840_);
lean_dec(v_x_1840_);
lean_dec(v_a_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v___x_1844_; 
v___x_1844_ = l_List_reverse___redArg(v_a_1843_);
return v___x_1844_;
}
else
{
lean_object* v_head_1845_; lean_object* v_tail_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v_head_1845_ = lean_ctor_get(v_a_1842_, 0);
v_tail_1846_ = lean_ctor_get(v_a_1842_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1848_ = v_a_1842_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_tail_1846_);
lean_inc(v_head_1845_);
lean_dec(v_a_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_Level_param___override(v_head_1845_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v_a_1843_);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1843_);
v___x_1852_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v_a_1842_ = v_tail_1846_;
v_a_1843_ = v___x_1852_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_1856_, size_t v_i_1857_, lean_object* v_bs_1858_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_usize_dec_lt(v_i_1857_, v_sz_1856_);
if (v___x_1859_ == 0)
{
return v_bs_1858_;
}
else
{
lean_object* v_v_1860_; lean_object* v___x_1861_; lean_object* v_bs_x27_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; 
v_v_1860_ = lean_array_uget(v_bs_1858_, v_i_1857_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v_bs_x27_1862_ = lean_array_uset(v_bs_1858_, v_i_1857_, v___x_1861_);
v___x_1863_ = l_Lean_JsonNumber_fromNat(v_v_1860_);
v___x_1864_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1857_, v___x_1865_);
v___x_1867_ = lean_array_uset(v_bs_x27_1862_, v_i_1857_, v___x_1864_);
v_i_1857_ = v___x_1866_;
v_bs_1858_ = v___x_1867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1869_, lean_object* v_i_1870_, lean_object* v_bs_1871_){
_start:
{
size_t v_sz_boxed_1872_; size_t v_i_boxed_1873_; lean_object* v_res_1874_; 
v_sz_boxed_1872_ = lean_unbox_usize(v_sz_1869_);
lean_dec(v_sz_1869_);
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_1872_, v_i_boxed_1873_, v_bs_1871_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_1875_){
_start:
{
size_t v_sz_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_sz_1876_ = lean_array_size(v_a_1875_);
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1876_, v___x_1877_, v_a_1875_);
v___x_1879_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_array_mk(v_a_1880_);
v___x_1882_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = l_List_reverse___redArg(v_x_1884_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v___y_1886_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
else
{
lean_object* v_head_1891_; lean_object* v_tail_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1912_; 
v_head_1891_ = lean_ctor_get(v_x_1883_, 0);
v_tail_1892_ = lean_ctor_get(v_x_1883_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1883_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1894_ = v_x_1883_;
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_tail_1892_);
lean_inc(v_head_1891_);
lean_dec(v_x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1912_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; 
v___x_1896_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_1891_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___x_1901_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v_fst_1898_ = lean_ctor_get(v_a_1897_, 0);
lean_inc(v_fst_1898_);
v_snd_1899_ = lean_ctor_get(v_a_1897_, 1);
lean_inc(v_snd_1899_);
lean_dec(v_a_1897_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v_x_1884_);
lean_ctor_set(v___x_1894_, 0, v_fst_1898_);
v___x_1901_ = v___x_1894_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_fst_1898_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_x_1884_);
v___x_1901_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_x_1883_ = v_tail_1892_;
v_x_1884_ = v___x_1901_;
v___y_1886_ = v_snd_1899_;
goto _start;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1894_);
lean_dec(v_tail_1892_);
lean_dec(v_x_1884_);
v_a_1904_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1896_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1896_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1913_, v_x_1914_, v___y_1915_, v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = l_List_reverse___redArg(v_x_1920_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1922_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v_head_1927_; lean_object* v_tail_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1948_; 
v_head_1927_ = lean_ctor_get(v_x_1919_, 0);
v_tail_1928_ = lean_ctor_get(v_x_1919_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_x_1919_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1930_ = v_x_1919_;
v_isShared_1931_ = v_isSharedCheck_1948_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_tail_1928_);
lean_inc(v_head_1927_);
lean_dec(v_x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1948_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_1927_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1937_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_fst_1934_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_fst_1934_);
v_snd_1935_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1935_);
lean_dec(v_a_1933_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_x_1920_);
lean_ctor_set(v___x_1930_, 0, v_fst_1934_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1934_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_x_1920_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
v_x_1919_ = v_tail_1928_;
v_x_1920_ = v___x_1937_;
v___y_1922_ = v_snd_1935_;
goto _start;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1930_);
lean_dec(v_tail_1928_);
lean_dec(v_x_1920_);
v_a_1940_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1932_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1932_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1949_, v_x_1950_, v___y_1951_, v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_box(0);
lean_inc(v_uparams_1955_);
v___x_1960_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_1955_, v___x_1959_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v_fst_1962_ = lean_ctor_get(v_a_1961_, 0);
lean_inc(v_fst_1962_);
v_snd_1963_ = lean_ctor_get(v_a_1961_, 1);
lean_inc(v_snd_1963_);
lean_dec(v_a_1961_);
v___x_1964_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_1955_, v___x_1959_);
v___x_1965_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_1964_, v___x_1959_, v_a_1956_, v_snd_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1983_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1981_; 
v_snd_1970_ = lean_ctor_get(v_a_1966_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_a_1966_, 0);
lean_dec(v_unused_1982_);
v___x_1972_ = v_a_1966_;
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_dec(v_a_1966_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_1962_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_snd_1970_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1976_);
v___x_1978_ = v___x_1968_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_fst_1962_);
v_a_1984_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1965_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1965_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_uparams_1955_);
v_a_1992_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1960_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1960_);
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
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v_a_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2005_, v___x_2009_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2028_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2028_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_fst_2015_; lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2027_; 
v_fst_2015_ = lean_ctor_get(v_a_2011_, 0);
v_snd_2016_ = lean_ctor_get(v_a_2011_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2018_ = v_a_2011_;
v_isShared_2019_ = v_isSharedCheck_2027_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_inc(v_fst_2015_);
lean_dec(v_a_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2027_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2015_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2016_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2022_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2010_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2010_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2037_, v_a_2038_, v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_11487__overap_2060_; lean_object* v___x_2061_; 
v___x_2046_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2047_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2047_, 0, v___x_2046_);
v___f_2048_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2048_, 0, v___x_2046_);
v___f_2049_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2049_, 0, v___x_2046_);
v___f_2050_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2050_, 0, v___x_2046_);
v___x_2051_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2051_, 0, lean_box(0));
lean_closure_set(v___x_2051_, 1, lean_box(0));
lean_closure_set(v___x_2051_, 2, v___x_2046_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___f_2047_);
v___x_2053_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2053_, 0, lean_box(0));
lean_closure_set(v___x_2053_, 1, lean_box(0));
lean_closure_set(v___x_2053_, 2, v___x_2046_);
v___x_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_ctor_set(v___x_2054_, 2, v___f_2048_);
lean_ctor_set(v___x_2054_, 3, v___f_2049_);
lean_ctor_set(v___x_2054_, 4, v___f_2050_);
v___x_2055_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2055_, 0, lean_box(0));
lean_closure_set(v___x_2055_, 1, lean_box(0));
lean_closure_set(v___x_2055_, 2, v___x_2046_);
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_instInhabitedExpr;
v___x_2058_ = l_instInhabitedOfMonad___redArg(v___x_2056_, v___x_2057_);
v___f_2059_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2059_, 0, v___x_2058_);
v___x_11487__overap_2060_ = lean_panic_fn_borrowed(v___f_2059_, v_msg_2042_);
lean_dec_ref(v___f_2059_);
lean_inc_ref(v___y_2043_);
v___x_2061_ = lean_apply_3(v___x_11487__overap_2060_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2062_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2067_, lean_object* v_b_2068_, lean_object* v_x_2069_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_dec(v_b_2068_);
lean_dec_ref(v_a_2067_);
return v_x_2069_;
}
else
{
lean_object* v_key_2070_; lean_object* v_value_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2084_; 
v_key_2070_ = lean_ctor_get(v_x_2069_, 0);
v_value_2071_ = lean_ctor_get(v_x_2069_, 1);
v_tail_2072_ = lean_ctor_get(v_x_2069_, 2);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2074_ = v_x_2069_;
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_value_2071_);
lean_inc(v_key_2070_);
lean_dec(v_x_2069_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2084_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_expr_eqv(v_key_2070_, v_a_2067_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2067_, v_b_2068_, v_tail_2072_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_key_2070_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_value_2071_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v___x_2077_);
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
lean_object* v___x_2082_; 
lean_dec(v_value_2071_);
lean_dec(v_key_2070_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v_b_2068_);
lean_ctor_set(v___x_2074_, 0, v_a_2067_);
v___x_2082_ = v___x_2074_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_b_2068_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_tail_2072_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
return v_x_2085_;
}
else
{
lean_object* v_key_2087_; lean_object* v_value_2088_; lean_object* v_tail_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2112_; 
v_key_2087_ = lean_ctor_get(v_x_2086_, 0);
v_value_2088_ = lean_ctor_get(v_x_2086_, 1);
v_tail_2089_ = lean_ctor_get(v_x_2086_, 2);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2091_ = v_x_2086_;
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_tail_2089_);
lean_inc(v_value_2088_);
lean_inc(v_key_2087_);
lean_dec(v_x_2086_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v_fold_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2093_ = lean_array_get_size(v_x_2085_);
v___x_2094_ = l_Lean_Expr_hash(v_key_2087_);
v___x_2095_ = 32ULL;
v___x_2096_ = lean_uint64_shift_right(v___x_2094_, v___x_2095_);
v_fold_2097_ = lean_uint64_xor(v___x_2094_, v___x_2096_);
v___x_2098_ = 16ULL;
v___x_2099_ = lean_uint64_shift_right(v_fold_2097_, v___x_2098_);
v___x_2100_ = lean_uint64_xor(v_fold_2097_, v___x_2099_);
v___x_2101_ = lean_uint64_to_usize(v___x_2100_);
v___x_2102_ = lean_usize_of_nat(v___x_2093_);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_sub(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_usize_land(v___x_2101_, v___x_2104_);
v___x_2106_ = lean_array_uget_borrowed(v_x_2085_, v___x_2105_);
lean_inc(v___x_2106_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 2, v___x_2106_);
v___x_2108_ = v___x_2091_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_key_2087_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_value_2088_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_array_uset(v_x_2085_, v___x_2105_, v___x_2108_);
v_x_2085_ = v___x_2109_;
v_x_2086_ = v_tail_2089_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2113_, lean_object* v_source_2114_, lean_object* v_target_2115_){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_array_get_size(v_source_2114_);
v___x_2117_ = lean_nat_dec_lt(v_i_2113_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_dec_ref(v_source_2114_);
lean_dec(v_i_2113_);
return v_target_2115_;
}
else
{
lean_object* v_es_2118_; lean_object* v___x_2119_; lean_object* v_source_2120_; lean_object* v_target_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_es_2118_ = lean_array_fget(v_source_2114_, v_i_2113_);
v___x_2119_ = lean_box(0);
v_source_2120_ = lean_array_fset(v_source_2114_, v_i_2113_, v___x_2119_);
v_target_2121_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2115_, v_es_2118_);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_i_2113_, v___x_2122_);
lean_dec(v_i_2113_);
v_i_2113_ = v___x_2123_;
v_source_2114_ = v_source_2120_;
v_target_2115_ = v_target_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_nbuckets_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2126_ = lean_array_get_size(v_data_2125_);
v___x_2127_ = lean_unsigned_to_nat(2u);
v_nbuckets_2128_ = lean_nat_mul(v___x_2126_, v___x_2127_);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_mk_array(v_nbuckets_2128_, v___x_2130_);
v___x_2132_ = lean_array_propagate_mark(v_data_2125_, v___x_2131_);
v___x_2133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2129_, v_data_2125_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = 0;
return v___x_2136_;
}
else
{
lean_object* v_key_2137_; lean_object* v_tail_2138_; uint8_t v___x_2139_; 
v_key_2137_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2138_ = lean_ctor_get(v_x_2135_, 2);
v___x_2139_ = lean_expr_eqv(v_key_2137_, v_a_2134_);
if (v___x_2139_ == 0)
{
v_x_2135_ = v_tail_2138_;
goto _start;
}
else
{
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2141_, lean_object* v_x_2142_){
_start:
{
uint8_t v_res_2143_; lean_object* v_r_2144_; 
v_res_2143_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec_ref(v_a_2141_);
v_r_2144_ = lean_box(v_res_2143_);
return v_r_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2145_, lean_object* v_a_2146_, lean_object* v_b_2147_){
_start:
{
lean_object* v_size_2148_; lean_object* v_buckets_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2192_; 
v_size_2148_ = lean_ctor_get(v_m_2145_, 0);
v_buckets_2149_ = lean_ctor_get(v_m_2145_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_m_2145_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2151_ = v_m_2145_;
v_isShared_2152_ = v_isSharedCheck_2192_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_buckets_2149_);
lean_inc(v_size_2148_);
lean_dec(v_m_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2192_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v_fold_2157_; uint64_t v___x_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; size_t v___x_2165_; lean_object* v_bkt_2166_; uint8_t v___x_2167_; 
v___x_2153_ = lean_array_get_size(v_buckets_2149_);
v___x_2154_ = l_Lean_Expr_hash(v_a_2146_);
v___x_2155_ = 32ULL;
v___x_2156_ = lean_uint64_shift_right(v___x_2154_, v___x_2155_);
v_fold_2157_ = lean_uint64_xor(v___x_2154_, v___x_2156_);
v___x_2158_ = 16ULL;
v___x_2159_ = lean_uint64_shift_right(v_fold_2157_, v___x_2158_);
v___x_2160_ = lean_uint64_xor(v_fold_2157_, v___x_2159_);
v___x_2161_ = lean_uint64_to_usize(v___x_2160_);
v___x_2162_ = lean_usize_of_nat(v___x_2153_);
v___x_2163_ = ((size_t)1ULL);
v___x_2164_ = lean_usize_sub(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_usize_land(v___x_2161_, v___x_2164_);
v_bkt_2166_ = lean_array_uget_borrowed(v_buckets_2149_, v___x_2165_);
v___x_2167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2146_, v_bkt_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_size_x27_2169_; lean_object* v___x_2170_; lean_object* v_buckets_x27_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2168_ = lean_unsigned_to_nat(1u);
v_size_x27_2169_ = lean_nat_add(v_size_2148_, v___x_2168_);
lean_dec(v_size_2148_);
lean_inc(v_bkt_2166_);
v___x_2170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2146_);
lean_ctor_set(v___x_2170_, 1, v_b_2147_);
lean_ctor_set(v___x_2170_, 2, v_bkt_2166_);
v_buckets_x27_2171_ = lean_array_uset(v_buckets_2149_, v___x_2165_, v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(4u);
v___x_2173_ = lean_nat_mul(v_size_x27_2169_, v___x_2172_);
v___x_2174_ = lean_unsigned_to_nat(3u);
v___x_2175_ = lean_nat_div(v___x_2173_, v___x_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_array_get_size(v_buckets_x27_2171_);
v___x_2177_ = lean_nat_dec_le(v___x_2175_, v___x_2176_);
lean_dec(v___x_2175_);
if (v___x_2177_ == 0)
{
lean_object* v_val_2178_; lean_object* v___x_2180_; 
v_val_2178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2171_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_val_2178_);
lean_ctor_set(v___x_2151_, 0, v_size_x27_2169_);
v___x_2180_ = v___x_2151_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_size_x27_2169_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_val_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2183_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_buckets_x27_2171_);
lean_ctor_set(v___x_2151_, 0, v_size_x27_2169_);
v___x_2183_ = v___x_2151_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_size_x27_2169_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_buckets_x27_2171_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v_buckets_x27_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_inc(v_bkt_2166_);
v___x_2185_ = lean_box(0);
v_buckets_x27_2186_ = lean_array_uset(v_buckets_2149_, v___x_2165_, v___x_2185_);
v___x_2187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2146_, v_b_2147_, v_bkt_2166_);
v___x_2188_ = lean_array_uset(v_buckets_x27_2186_, v___x_2165_, v___x_2187_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2188_);
v___x_2190_ = v___x_2151_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_size_2148_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_box(0);
return v___x_2195_;
}
else
{
lean_object* v_key_2196_; lean_object* v_value_2197_; lean_object* v_tail_2198_; uint8_t v___x_2199_; 
v_key_2196_ = lean_ctor_get(v_x_2194_, 0);
v_value_2197_ = lean_ctor_get(v_x_2194_, 1);
v_tail_2198_ = lean_ctor_get(v_x_2194_, 2);
v___x_2199_ = lean_expr_eqv(v_key_2196_, v_a_2193_);
if (v___x_2199_ == 0)
{
v_x_2194_ = v_tail_2198_;
goto _start;
}
else
{
lean_object* v___x_2201_; 
lean_inc(v_value_2197_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_value_2197_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2202_, v_x_2203_);
lean_dec(v_x_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_buckets_2207_; lean_object* v___x_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v_fold_2212_; uint64_t v___x_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_buckets_2207_ = lean_ctor_get(v_m_2205_, 1);
v___x_2208_ = lean_array_get_size(v_buckets_2207_);
v___x_2209_ = l_Lean_Expr_hash(v_a_2206_);
v___x_2210_ = 32ULL;
v___x_2211_ = lean_uint64_shift_right(v___x_2209_, v___x_2210_);
v_fold_2212_ = lean_uint64_xor(v___x_2209_, v___x_2211_);
v___x_2213_ = 16ULL;
v___x_2214_ = lean_uint64_shift_right(v_fold_2212_, v___x_2213_);
v___x_2215_ = lean_uint64_xor(v_fold_2212_, v___x_2214_);
v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
v___x_2217_ = lean_usize_of_nat(v___x_2208_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_sub(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_usize_land(v___x_2216_, v___x_2219_);
v___x_2221_ = lean_array_uget_borrowed(v_buckets_2207_, v___x_2220_);
v___x_2222_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2206_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2223_, v_a_2224_);
lean_dec_ref(v_a_2224_);
lean_dec_ref(v_m_2223_);
return v_res_2225_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2227_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2228_ = lean_unsigned_to_nat(26u);
v___x_2229_ = lean_unsigned_to_nat(152u);
v___x_2230_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2231_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2232_ = l_mkPanicMessageWithDecl(v___x_2231_, v___x_2230_, v___x_2229_, v___x_2228_, v___x_2227_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_e_x27_2238_; lean_object* v_visitedNames_2239_; lean_object* v_visitedLevels_2240_; lean_object* v_visitedExprs_2241_; lean_object* v_visitedConstants_2242_; lean_object* v_noMDataExprs_2243_; uint8_t v_exportMData_2244_; uint8_t v_exportUnsafe_2245_; uint8_t v_ignoreMissing_2246_; lean_object* v_recursorMap_2247_; lean_object* v_e_x27_2253_; lean_object* v___y_2254_; lean_object* v_visitedNames_2264_; lean_object* v_visitedLevels_2265_; lean_object* v_visitedExprs_2266_; lean_object* v_visitedConstants_2267_; lean_object* v_noMDataExprs_2268_; uint8_t v_exportMData_2269_; uint8_t v_exportUnsafe_2270_; uint8_t v_ignoreMissing_2271_; lean_object* v_recursorMap_2272_; lean_object* v___x_2273_; 
v_visitedNames_2264_ = lean_ctor_get(v_a_2235_, 0);
v_visitedLevels_2265_ = lean_ctor_get(v_a_2235_, 1);
v_visitedExprs_2266_ = lean_ctor_get(v_a_2235_, 2);
v_visitedConstants_2267_ = lean_ctor_get(v_a_2235_, 3);
v_noMDataExprs_2268_ = lean_ctor_get(v_a_2235_, 4);
v_exportMData_2269_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6);
v_exportUnsafe_2270_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6 + 1);
v_ignoreMissing_2271_ = lean_ctor_get_uint8(v_a_2235_, sizeof(void*)*6 + 2);
v_recursorMap_2272_ = lean_ctor_get(v_a_2235_, 5);
v___x_2273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2268_, v_e_2233_);
if (lean_obj_tag(v___x_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_e_2233_);
v_val_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_val_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_val_2274_);
lean_ctor_set(v___x_2278_, 1, v_a_2235_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_dec(v___x_2273_);
switch(lean_obj_tag(v_e_2233_))
{
case 1:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2284_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2283_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v_fst_2286_ = lean_ctor_get(v_a_2285_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v_a_2285_, 1);
lean_inc(v_snd_2287_);
lean_dec(v_a_2285_);
v_e_x27_2253_ = v_fst_2286_;
v___y_2254_ = v_snd_2287_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 1);
return v___x_2284_;
}
}
case 2:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2289_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2288_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_fst_2291_ = lean_ctor_get(v_a_2290_, 0);
lean_inc(v_fst_2291_);
v_snd_2292_ = lean_ctor_get(v_a_2290_, 1);
lean_inc(v_snd_2292_);
lean_dec(v_a_2290_);
v_e_x27_2253_ = v_fst_2291_;
v___y_2254_ = v_snd_2292_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 1);
return v___x_2289_;
}
}
case 5:
{
lean_object* v_fn_2293_; lean_object* v_arg_2294_; lean_object* v___x_2295_; 
v_fn_2293_ = lean_ctor_get(v_e_2233_, 0);
v_arg_2294_ = lean_ctor_get(v_e_2233_, 1);
lean_inc_ref(v_fn_2293_);
v___x_2295_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2293_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v_fst_2297_; lean_object* v_snd_2298_; lean_object* v___x_2299_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v_fst_2297_ = lean_ctor_get(v_a_2296_, 0);
lean_inc(v_fst_2297_);
v_snd_2298_ = lean_ctor_get(v_a_2296_, 1);
lean_inc(v_snd_2298_);
lean_dec(v_a_2296_);
lean_inc_ref(v_arg_2294_);
v___x_2299_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2294_, v_a_2234_, v_snd_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_fst_2301_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v_a_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_a_2300_);
v___x_2303_ = lean_ptr_addr(v_fn_2293_);
v___x_2304_ = lean_ptr_addr(v_fst_2297_);
v___x_2305_ = lean_usize_dec_eq(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Expr_app___override(v_fst_2297_, v_fst_2301_);
v_e_x27_2253_ = v___x_2306_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
else
{
size_t v___x_2307_; size_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = lean_ptr_addr(v_arg_2294_);
v___x_2308_ = lean_ptr_addr(v_fst_2301_);
v___x_2309_ = lean_usize_dec_eq(v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Expr_app___override(v_fst_2297_, v_fst_2301_);
v_e_x27_2253_ = v___x_2310_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2301_);
lean_dec(v_fst_2297_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2302_;
goto v___jp_2252_;
}
}
}
else
{
lean_dec(v_fst_2297_);
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2299_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2295_;
}
}
case 6:
{
lean_object* v_binderName_2311_; lean_object* v_binderType_2312_; lean_object* v_body_2313_; uint8_t v_binderInfo_2314_; lean_object* v___x_2315_; 
v_binderName_2311_ = lean_ctor_get(v_e_2233_, 0);
v_binderType_2312_ = lean_ctor_get(v_e_2233_, 1);
v_body_2313_ = lean_ctor_get(v_e_2233_, 2);
v_binderInfo_2314_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2312_);
v___x_2315_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2312_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_fst_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_fst_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_fst_2317_);
v_snd_2318_ = lean_ctor_get(v_a_2316_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2316_);
lean_inc_ref(v_body_2313_);
v___x_2319_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2313_, v_a_2234_, v_snd_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; size_t v___x_2323_; size_t v___x_2324_; uint8_t v___x_2325_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_fst_2321_ = lean_ctor_get(v_a_2320_, 0);
lean_inc(v_fst_2321_);
v_snd_2322_ = lean_ctor_get(v_a_2320_, 1);
lean_inc(v_snd_2322_);
lean_dec(v_a_2320_);
v___x_2323_ = lean_ptr_addr(v_binderType_2312_);
v___x_2324_ = lean_ptr_addr(v_fst_2317_);
v___x_2325_ = lean_usize_dec_eq(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_inc(v_binderName_2311_);
v___x_2326_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2326_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
size_t v___x_2327_; size_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_ptr_addr(v_body_2313_);
v___x_2328_ = lean_ptr_addr(v_fst_2321_);
v___x_2329_ = lean_usize_dec_eq(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_inc(v_binderName_2311_);
v___x_2330_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2330_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
uint8_t v___x_2331_; 
v___x_2331_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2314_, v_binderInfo_2314_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_inc(v_binderName_2311_);
v___x_2332_ = l_Lean_Expr_lam___override(v_binderName_2311_, v_fst_2317_, v_fst_2321_, v_binderInfo_2314_);
v_e_x27_2253_ = v___x_2332_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2321_);
lean_dec(v_fst_2317_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2322_;
goto v___jp_2252_;
}
}
}
}
else
{
lean_dec(v_fst_2317_);
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2319_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2315_;
}
}
case 7:
{
lean_object* v_binderName_2333_; lean_object* v_binderType_2334_; lean_object* v_body_2335_; uint8_t v_binderInfo_2336_; lean_object* v___x_2337_; 
v_binderName_2333_ = lean_ctor_get(v_e_2233_, 0);
v_binderType_2334_ = lean_ctor_get(v_e_2233_, 1);
v_body_2335_ = lean_ctor_get(v_e_2233_, 2);
v_binderInfo_2336_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2334_);
v___x_2337_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2334_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_fst_2339_; lean_object* v_snd_2340_; lean_object* v___x_2341_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v_fst_2339_ = lean_ctor_get(v_a_2338_, 0);
lean_inc(v_fst_2339_);
v_snd_2340_ = lean_ctor_get(v_a_2338_, 1);
lean_inc(v_snd_2340_);
lean_dec(v_a_2338_);
lean_inc_ref(v_body_2335_);
v___x_2341_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2335_, v_a_2234_, v_snd_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v_fst_2343_; lean_object* v_snd_2344_; size_t v___x_2345_; size_t v___x_2346_; uint8_t v___x_2347_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v_fst_2343_ = lean_ctor_get(v_a_2342_, 0);
lean_inc(v_fst_2343_);
v_snd_2344_ = lean_ctor_get(v_a_2342_, 1);
lean_inc(v_snd_2344_);
lean_dec(v_a_2342_);
v___x_2345_ = lean_ptr_addr(v_binderType_2334_);
v___x_2346_ = lean_ptr_addr(v_fst_2339_);
v___x_2347_ = lean_usize_dec_eq(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_inc(v_binderName_2333_);
v___x_2348_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2348_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
size_t v___x_2349_; size_t v___x_2350_; uint8_t v___x_2351_; 
v___x_2349_ = lean_ptr_addr(v_body_2335_);
v___x_2350_ = lean_ptr_addr(v_fst_2343_);
v___x_2351_ = lean_usize_dec_eq(v___x_2349_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_inc(v_binderName_2333_);
v___x_2352_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2352_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
uint8_t v___x_2353_; 
v___x_2353_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2336_, v_binderInfo_2336_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_inc(v_binderName_2333_);
v___x_2354_ = l_Lean_Expr_forallE___override(v_binderName_2333_, v_fst_2339_, v_fst_2343_, v_binderInfo_2336_);
v_e_x27_2253_ = v___x_2354_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2343_);
lean_dec(v_fst_2339_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2344_;
goto v___jp_2252_;
}
}
}
}
else
{
lean_dec(v_fst_2339_);
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2341_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2337_;
}
}
case 8:
{
lean_object* v_declName_2355_; lean_object* v_type_2356_; lean_object* v_value_2357_; lean_object* v_body_2358_; uint8_t v_nondep_2359_; lean_object* v___x_2360_; 
v_declName_2355_ = lean_ctor_get(v_e_2233_, 0);
v_type_2356_ = lean_ctor_get(v_e_2233_, 1);
v_value_2357_ = lean_ctor_get(v_e_2233_, 2);
v_body_2358_ = lean_ctor_get(v_e_2233_, 3);
v_nondep_2359_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2356_);
v___x_2360_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2356_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_fst_2362_; lean_object* v_snd_2363_; lean_object* v___x_2364_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v_fst_2362_ = lean_ctor_get(v_a_2361_, 0);
lean_inc(v_fst_2362_);
v_snd_2363_ = lean_ctor_get(v_a_2361_, 1);
lean_inc(v_snd_2363_);
lean_dec(v_a_2361_);
lean_inc_ref(v_value_2357_);
v___x_2364_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2357_, v_a_2234_, v_snd_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_fst_2366_; lean_object* v_snd_2367_; lean_object* v___x_2368_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_fst_2366_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_fst_2366_);
v_snd_2367_ = lean_ctor_get(v_a_2365_, 1);
lean_inc(v_snd_2367_);
lean_dec(v_a_2365_);
lean_inc_ref(v_body_2358_);
v___x_2368_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2358_, v_a_2234_, v_snd_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_fst_2370_; lean_object* v_snd_2371_; uint8_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; uint8_t v___x_2375_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v_fst_2370_ = lean_ctor_get(v_a_2369_, 0);
lean_inc(v_fst_2370_);
v_snd_2371_ = lean_ctor_get(v_a_2369_, 1);
lean_inc(v_snd_2371_);
lean_dec(v_a_2369_);
v___x_2372_ = 0;
v___x_2373_ = lean_ptr_addr(v_type_2356_);
v___x_2374_ = lean_ptr_addr(v_fst_2362_);
v___x_2375_ = lean_usize_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_inc(v_declName_2355_);
v___x_2376_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2376_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
size_t v___x_2377_; size_t v___x_2378_; uint8_t v___x_2379_; 
v___x_2377_ = lean_ptr_addr(v_value_2357_);
v___x_2378_ = lean_ptr_addr(v_fst_2366_);
v___x_2379_ = lean_usize_dec_eq(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_inc(v_declName_2355_);
v___x_2380_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2380_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
size_t v___x_2381_; size_t v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_ptr_addr(v_body_2358_);
v___x_2382_ = lean_ptr_addr(v_fst_2370_);
v___x_2383_ = lean_usize_dec_eq(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
lean_inc(v_declName_2355_);
v___x_2384_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2384_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
if (v_nondep_2359_ == 0)
{
lean_dec(v_fst_2370_);
lean_dec(v_fst_2366_);
lean_dec(v_fst_2362_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2385_; 
lean_inc(v_declName_2355_);
v___x_2385_ = l_Lean_Expr_letE___override(v_declName_2355_, v_fst_2362_, v_fst_2366_, v_fst_2370_, v___x_2372_);
v_e_x27_2253_ = v___x_2385_;
v___y_2254_ = v_snd_2371_;
goto v___jp_2252_;
}
}
}
}
}
else
{
lean_dec(v_fst_2366_);
lean_dec(v_fst_2362_);
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2368_;
}
}
else
{
lean_dec(v_fst_2362_);
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2364_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 4);
return v___x_2360_;
}
}
case 10:
{
lean_object* v_expr_2386_; lean_object* v___x_2387_; 
v_expr_2386_ = lean_ctor_get(v_e_2233_, 1);
lean_inc_ref(v_expr_2386_);
v___x_2387_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2386_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v_fst_2389_; lean_object* v_snd_2390_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v_fst_2389_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_fst_2389_);
v_snd_2390_ = lean_ctor_get(v_a_2388_, 1);
lean_inc(v_snd_2390_);
lean_dec(v_a_2388_);
v_e_x27_2253_ = v_fst_2389_;
v___y_2254_ = v_snd_2390_;
goto v___jp_2252_;
}
else
{
lean_dec_ref_known(v_e_2233_, 2);
return v___x_2387_;
}
}
case 11:
{
lean_object* v_typeName_2391_; lean_object* v_idx_2392_; lean_object* v_struct_2393_; lean_object* v___x_2394_; 
v_typeName_2391_ = lean_ctor_get(v_e_2233_, 0);
v_idx_2392_ = lean_ctor_get(v_e_2233_, 1);
v_struct_2393_ = lean_ctor_get(v_e_2233_, 2);
lean_inc_ref(v_struct_2393_);
v___x_2394_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2393_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; size_t v___x_2398_; size_t v___x_2399_; uint8_t v___x_2400_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_fst_2396_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2396_);
v_snd_2397_ = lean_ctor_get(v_a_2395_, 1);
lean_inc(v_snd_2397_);
lean_dec(v_a_2395_);
v___x_2398_ = lean_ptr_addr(v_struct_2393_);
v___x_2399_ = lean_ptr_addr(v_fst_2396_);
v___x_2400_ = lean_usize_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_inc(v_idx_2392_);
lean_inc(v_typeName_2391_);
v___x_2401_ = l_Lean_Expr_proj___override(v_typeName_2391_, v_idx_2392_, v_fst_2396_);
v_e_x27_2253_ = v___x_2401_;
v___y_2254_ = v_snd_2397_;
goto v___jp_2252_;
}
else
{
lean_dec(v_fst_2396_);
lean_inc_ref(v_e_2233_);
v_e_x27_2253_ = v_e_2233_;
v___y_2254_ = v_snd_2397_;
goto v___jp_2252_;
}
}
else
{
lean_dec_ref_known(v_e_2233_, 3);
return v___x_2394_;
}
}
default: 
{
lean_inc(v_recursorMap_2272_);
lean_inc_ref(v_noMDataExprs_2268_);
lean_inc_ref(v_visitedConstants_2267_);
lean_inc_ref(v_visitedExprs_2266_);
lean_inc_ref(v_visitedLevels_2265_);
lean_inc_ref(v_visitedNames_2264_);
lean_dec_ref(v_a_2235_);
lean_inc_ref(v_e_2233_);
v_e_x27_2238_ = v_e_2233_;
v_visitedNames_2239_ = v_visitedNames_2264_;
v_visitedLevels_2240_ = v_visitedLevels_2265_;
v_visitedExprs_2241_ = v_visitedExprs_2266_;
v_visitedConstants_2242_ = v_visitedConstants_2267_;
v_noMDataExprs_2243_ = v_noMDataExprs_2268_;
v_exportMData_2244_ = v_exportMData_2269_;
v_exportUnsafe_2245_ = v_exportUnsafe_2270_;
v_ignoreMissing_2246_ = v_ignoreMissing_2271_;
v_recursorMap_2247_ = v_recursorMap_2272_;
goto v___jp_2237_;
}
}
}
v___jp_2237_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc_ref(v_e_x27_2238_);
v___x_2248_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2243_, v_e_2233_, v_e_x27_2238_);
v___x_2249_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2249_, 0, v_visitedNames_2239_);
lean_ctor_set(v___x_2249_, 1, v_visitedLevels_2240_);
lean_ctor_set(v___x_2249_, 2, v_visitedExprs_2241_);
lean_ctor_set(v___x_2249_, 3, v_visitedConstants_2242_);
lean_ctor_set(v___x_2249_, 4, v___x_2248_);
lean_ctor_set(v___x_2249_, 5, v_recursorMap_2247_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6, v_exportMData_2244_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6 + 1, v_exportUnsafe_2245_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*6 + 2, v_ignoreMissing_2246_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_e_x27_2238_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
v___jp_2252_:
{
lean_object* v_visitedNames_2255_; lean_object* v_visitedLevels_2256_; lean_object* v_visitedExprs_2257_; lean_object* v_visitedConstants_2258_; lean_object* v_noMDataExprs_2259_; uint8_t v_exportMData_2260_; uint8_t v_exportUnsafe_2261_; uint8_t v_ignoreMissing_2262_; lean_object* v_recursorMap_2263_; 
v_visitedNames_2255_ = lean_ctor_get(v___y_2254_, 0);
lean_inc_ref(v_visitedNames_2255_);
v_visitedLevels_2256_ = lean_ctor_get(v___y_2254_, 1);
lean_inc_ref(v_visitedLevels_2256_);
v_visitedExprs_2257_ = lean_ctor_get(v___y_2254_, 2);
lean_inc_ref(v_visitedExprs_2257_);
v_visitedConstants_2258_ = lean_ctor_get(v___y_2254_, 3);
lean_inc_ref(v_visitedConstants_2258_);
v_noMDataExprs_2259_ = lean_ctor_get(v___y_2254_, 4);
lean_inc_ref(v_noMDataExprs_2259_);
v_exportMData_2260_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6);
v_exportUnsafe_2261_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6 + 1);
v_ignoreMissing_2262_ = lean_ctor_get_uint8(v___y_2254_, sizeof(void*)*6 + 2);
v_recursorMap_2263_ = lean_ctor_get(v___y_2254_, 5);
lean_inc(v_recursorMap_2263_);
lean_dec_ref(v___y_2254_);
v_e_x27_2238_ = v_e_x27_2253_;
v_visitedNames_2239_ = v_visitedNames_2255_;
v_visitedLevels_2240_ = v_visitedLevels_2256_;
v_visitedExprs_2241_ = v_visitedExprs_2257_;
v_visitedConstants_2242_ = v_visitedConstants_2258_;
v_noMDataExprs_2243_ = v_noMDataExprs_2259_;
v_exportMData_2244_ = v_exportMData_2260_;
v_exportUnsafe_2245_ = v_exportUnsafe_2261_;
v_ignoreMissing_2246_ = v_ignoreMissing_2262_;
v_recursorMap_2247_ = v_recursorMap_2263_;
goto v___jp_2237_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_a_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2407_, lean_object* v_m_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2408_, v_a_2409_, v_b_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2412_, lean_object* v_m_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2413_, v_a_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_m_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2416_, v_m_2417_, v_a_2418_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_m_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2421_, v_x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2424_, lean_object* v_a_2425_, lean_object* v_x_2426_){
_start:
{
uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_res_2427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2424_, v_a_2425_, v_x_2426_);
lean_dec(v_x_2426_);
lean_dec_ref(v_a_2425_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2429_, lean_object* v_data_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2432_, lean_object* v_a_2433_, lean_object* v_b_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2433_, v_b_2434_, v_x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2438_, v_x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2441_, lean_object* v_a_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2441_, v_a_2442_, v_x_2443_);
lean_dec(v_x_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2445_, lean_object* v_i_2446_, lean_object* v_source_2447_, lean_object* v_target_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2446_, v_source_2447_, v_target_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2451_, v_x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = l_Lean_Json_mkObj(v_fields_2454_);
v___x_2458_ = l_Lean_Json_compress(v___x_2457_);
v___x_2459_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_a_2460_);
lean_ctor_set(v___x_2464_, 1, v_a_2455_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_a_2455_);
v_a_2469_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2459_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2459_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2477_, v_a_2478_);
lean_dec(v_fields_2477_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2481_, v_a_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2486_, v_a_2487_, v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_fields_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2491_, lean_object* v_k_2492_){
_start:
{
if (lean_obj_tag(v_t_2491_) == 0)
{
lean_object* v_k_2493_; lean_object* v_v_2494_; lean_object* v_l_2495_; lean_object* v_r_2496_; uint8_t v___x_2497_; 
v_k_2493_ = lean_ctor_get(v_t_2491_, 1);
v_v_2494_ = lean_ctor_get(v_t_2491_, 2);
v_l_2495_ = lean_ctor_get(v_t_2491_, 3);
v_r_2496_ = lean_ctor_get(v_t_2491_, 4);
v___x_2497_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2492_, v_k_2493_);
switch(v___x_2497_)
{
case 0:
{
v_t_2491_ = v_l_2495_;
goto _start;
}
case 1:
{
lean_object* v___x_2499_; 
lean_inc(v_v_2494_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_v_2494_);
return v___x_2499_;
}
default: 
{
v_t_2491_ = v_r_2496_;
goto _start;
}
}
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_box(0);
return v___x_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2502_, v_k_2503_);
lean_dec(v_k_2503_);
lean_dec(v_t_2502_);
return v_res_2504_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Array_instInhabited___redArg();
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_163477__overap_2525_; lean_object* v___x_2526_; 
v___x_2510_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2511_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2511_, 0, v___x_2510_);
v___f_2512_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2512_, 0, v___x_2510_);
v___f_2513_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2513_, 0, v___x_2510_);
v___f_2514_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2514_, 0, v___x_2510_);
v___x_2515_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2515_, 0, lean_box(0));
lean_closure_set(v___x_2515_, 1, lean_box(0));
lean_closure_set(v___x_2515_, 2, v___x_2510_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___f_2511_);
v___x_2517_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2517_, 0, lean_box(0));
lean_closure_set(v___x_2517_, 1, lean_box(0));
lean_closure_set(v___x_2517_, 2, v___x_2510_);
v___x_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
lean_ctor_set(v___x_2518_, 2, v___f_2512_);
lean_ctor_set(v___x_2518_, 3, v___f_2513_);
lean_ctor_set(v___x_2518_, 4, v___f_2514_);
v___x_2519_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2519_, 0, lean_box(0));
lean_closure_set(v___x_2519_, 1, lean_box(0));
lean_closure_set(v___x_2519_, 2, v___x_2510_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
v___x_2523_ = l_instInhabitedOfMonad___redArg(v___x_2520_, v___x_2522_);
v___f_2524_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2524_, 0, v___x_2523_);
v___x_163477__overap_2525_ = lean_panic_fn_borrowed(v___f_2524_, v_msg_2506_);
lean_dec_ref(v___f_2524_);
lean_inc_ref(v___y_2507_);
v___x_2526_ = lean_apply_3(v___x_163477__overap_2525_, v___y_2507_, v___y_2508_, lean_box(0));
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2527_, v___y_2528_, v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___f_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; lean_object* v___x_162755__overap_2550_; lean_object* v___x_2551_; 
v___x_2536_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2537_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2537_, 0, v___x_2536_);
v___f_2538_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2538_, 0, v___x_2536_);
v___f_2539_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2539_, 0, v___x_2536_);
v___f_2540_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2540_, 0, v___x_2536_);
v___x_2541_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2541_, 0, lean_box(0));
lean_closure_set(v___x_2541_, 1, lean_box(0));
lean_closure_set(v___x_2541_, 2, v___x_2536_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___f_2537_);
v___x_2543_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2543_, 0, lean_box(0));
lean_closure_set(v___x_2543_, 1, lean_box(0));
lean_closure_set(v___x_2543_, 2, v___x_2536_);
v___x_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_ctor_set(v___x_2544_, 2, v___f_2538_);
lean_ctor_set(v___x_2544_, 3, v___f_2539_);
lean_ctor_set(v___x_2544_, 4, v___f_2540_);
v___x_2545_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2545_, 0, lean_box(0));
lean_closure_set(v___x_2545_, 1, lean_box(0));
lean_closure_set(v___x_2545_, 2, v___x_2536_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_box(0);
v___x_2548_ = l_instInhabitedOfMonad___redArg(v___x_2546_, v___x_2547_);
v___f_2549_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2549_, 0, v___x_2548_);
v___x_162755__overap_2550_ = lean_panic_fn_borrowed(v___f_2549_, v_msg_2532_);
lean_dec_ref(v___f_2549_);
lean_inc_ref(v___y_2533_);
v___x_2551_ = lean_apply_3(v___x_162755__overap_2550_, v___y_2533_, v___y_2534_, lean_box(0));
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2552_, v___y_2553_, v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2559_ = lean_panic_fn_borrowed(v___x_2558_, v_msg_2557_);
return v___x_2559_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1));
v___x_2563_ = lean_unsigned_to_nat(10u);
v___x_2564_ = lean_unsigned_to_nat(334u);
v___x_2565_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2566_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2567_ = l_mkPanicMessageWithDecl(v___x_2566_, v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_);
return v___x_2567_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3));
v___x_2570_ = lean_unsigned_to_nat(15u);
v___x_2571_ = lean_unsigned_to_nat(336u);
v___x_2572_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2573_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2574_ = l_mkPanicMessageWithDecl(v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_);
return v___x_2574_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2578_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7));
v___x_2579_ = lean_unsigned_to_nat(14u);
v___x_2580_ = lean_unsigned_to_nat(22u);
v___x_2581_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6));
v___x_2582_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5));
v___x_2583_ = l_mkPanicMessageWithDecl(v___x_2582_, v___x_2581_, v___x_2580_, v___x_2579_, v___x_2578_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2584_, uint8_t v___x_2585_, lean_object* v_as_x27_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
if (lean_obj_tag(v_as_x27_2586_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_b_2587_);
lean_ctor_set(v___x_2591_, 1, v___y_2589_);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v___y_2596_; lean_object* v___y_2600_; uint8_t v___y_2601_; lean_object* v___y_2636_; lean_object* v___x_2652_; 
v_head_2593_ = lean_ctor_get(v_as_x27_2586_, 0);
v_tail_2594_ = lean_ctor_get(v_as_x27_2586_, 1);
lean_inc(v_head_2593_);
lean_inc_ref(v___y_2588_);
v___x_2652_ = l_Lean_Environment_find_x3f(v___y_2588_, v_head_2593_, v___x_2585_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2654_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2653_);
v___y_2636_ = v___x_2654_;
goto v___jp_2635_;
}
else
{
lean_object* v_val_2655_; 
v_val_2655_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_val_2655_);
lean_dec_ref_known(v___x_2652_, 1);
v___y_2636_ = v_val_2655_;
goto v___jp_2635_;
}
v___jp_2595_:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_array_push(v_b_2587_, v___y_2596_);
v_as_x27_2586_ = v_tail_2594_;
v_b_2587_ = v___x_2597_;
goto _start;
}
v___jp_2599_:
{
if (v___y_2601_ == 0)
{
uint8_t v_exportUnsafe_2602_; 
v_exportUnsafe_2602_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref(v___y_2600_);
lean_dec_ref(v_b_2587_);
v___x_2603_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2);
v___x_2604_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2603_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2626_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2626_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2626_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fst_2609_; 
v_fst_2609_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_fst_2609_);
if (lean_obj_tag(v_fst_2609_) == 0)
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2621_; 
v_snd_2610_ = lean_ctor_get(v_a_2605_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_a_2605_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v_a_2605_, 0);
lean_dec(v_unused_2622_);
v___x_2612_ = v_a_2605_;
v_isShared_2613_ = v_isSharedCheck_2621_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_dec(v_a_2605_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2621_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v_a_2614_; lean_object* v___x_2616_; 
v_a_2614_ = lean_ctor_get(v_fst_2609_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v_fst_2609_, 1);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_a_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_snd_2610_);
v___x_2616_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2618_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2616_);
v___x_2618_ = v___x_2607_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_snd_2623_; lean_object* v_a_2624_; 
lean_del_object(v___x_2607_);
v_snd_2623_ = lean_ctor_get(v_a_2605_, 1);
lean_inc(v_snd_2623_);
lean_dec(v_a_2605_);
v_a_2624_ = lean_ctor_get(v_fst_2609_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v_fst_2609_, 1);
v_as_x27_2586_ = v_tail_2594_;
v_b_2587_ = v_a_2624_;
v___y_2589_ = v_snd_2623_;
goto _start;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_a_2627_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2604_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2604_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
v___y_2596_ = v___y_2600_;
goto v___jp_2595_;
}
}
else
{
v___y_2596_ = v___y_2600_;
goto v___jp_2595_;
}
}
v___jp_2635_:
{
if (lean_obj_tag(v___y_2636_) == 6)
{
lean_object* v_val_2637_; uint8_t v_isUnsafe_2638_; 
v_val_2637_ = lean_ctor_get(v___y_2636_, 0);
lean_inc_ref(v_val_2637_);
lean_dec_ref_known(v___y_2636_, 1);
v_isUnsafe_2638_ = lean_ctor_get_uint8(v_val_2637_, sizeof(void*)*5);
if (v_isUnsafe_2638_ == 0)
{
v___y_2600_ = v_val_2637_;
v___y_2601_ = v___y_2584_;
goto v___jp_2599_;
}
else
{
v___y_2600_ = v_val_2637_;
v___y_2601_ = v___x_2585_;
goto v___jp_2599_;
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec_ref(v___y_2636_);
v___x_2639_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4);
v___x_2640_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2639_, v___y_2588_, v___y_2589_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v_snd_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v_snd_2642_ = lean_ctor_get(v_a_2641_, 1);
lean_inc(v_snd_2642_);
lean_dec(v_a_2641_);
v_as_x27_2586_ = v_tail_2594_;
v___y_2589_ = v_snd_2642_;
goto _start;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_b_2587_);
v_a_2644_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2640_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2656_, lean_object* v___x_2657_, lean_object* v_as_x27_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v___y_172079__boxed_2663_; uint8_t v___x_172080__boxed_2664_; lean_object* v_res_2665_; 
v___y_172079__boxed_2663_ = lean_unbox(v___y_2656_);
v___x_172080__boxed_2664_ = lean_unbox(v___x_2657_);
v_res_2665_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172079__boxed_2663_, v___x_172080__boxed_2664_, v_as_x27_2658_, v_b_2659_, v___y_2660_, v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v_as_x27_2658_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___x_164159__overap_2688_; lean_object* v___x_2689_; 
v___x_2670_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2671_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2671_, 0, v___x_2670_);
v___f_2672_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2672_, 0, v___x_2670_);
v___f_2673_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2673_, 0, v___x_2670_);
v___f_2674_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2674_, 0, v___x_2670_);
v___x_2675_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2675_, 0, lean_box(0));
lean_closure_set(v___x_2675_, 1, lean_box(0));
lean_closure_set(v___x_2675_, 2, v___x_2670_);
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v___f_2671_);
v___x_2677_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2677_, 0, lean_box(0));
lean_closure_set(v___x_2677_, 1, lean_box(0));
lean_closure_set(v___x_2677_, 2, v___x_2670_);
v___x_2678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
lean_ctor_set(v___x_2678_, 2, v___f_2672_);
lean_ctor_set(v___x_2678_, 3, v___f_2673_);
lean_ctor_set(v___x_2678_, 4, v___f_2674_);
v___x_2679_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2679_, 0, lean_box(0));
lean_closure_set(v___x_2679_, 1, lean_box(0));
lean_closure_set(v___x_2679_, 2, v___x_2670_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2682_ = lean_box(1);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
v___x_2686_ = l_instInhabitedOfMonad___redArg(v___x_2680_, v___x_2685_);
v___f_2687_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2687_, 0, v___x_2686_);
v___x_164159__overap_2688_ = lean_panic_fn_borrowed(v___f_2687_, v_msg_2666_);
lean_dec_ref(v___f_2687_);
lean_inc_ref(v___y_2667_);
v___x_2689_ = lean_apply_3(v___x_164159__overap_2688_, v___y_2667_, v___y_2668_, lean_box(0));
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2690_, v___y_2691_, v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_162743__overap_2714_; lean_object* v___x_2715_; 
v___x_2699_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2700_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2700_, 0, v___x_2699_);
v___f_2701_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2701_, 0, v___x_2699_);
v___f_2702_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2702_, 0, v___x_2699_);
v___f_2703_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2703_, 0, v___x_2699_);
v___x_2704_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2704_, 0, lean_box(0));
lean_closure_set(v___x_2704_, 1, lean_box(0));
lean_closure_set(v___x_2704_, 2, v___x_2699_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___f_2700_);
v___x_2706_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2706_, 0, lean_box(0));
lean_closure_set(v___x_2706_, 1, lean_box(0));
lean_closure_set(v___x_2706_, 2, v___x_2699_);
v___x_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
lean_ctor_set(v___x_2707_, 2, v___f_2701_);
lean_ctor_set(v___x_2707_, 3, v___f_2702_);
lean_ctor_set(v___x_2707_, 4, v___f_2703_);
v___x_2708_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2708_, 0, lean_box(0));
lean_closure_set(v___x_2708_, 1, lean_box(0));
lean_closure_set(v___x_2708_, 2, v___x_2699_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
v___x_2712_ = l_instInhabitedOfMonad___redArg(v___x_2709_, v___x_2711_);
v___f_2713_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2713_, 0, v___x_2712_);
v___x_162743__overap_2714_ = lean_panic_fn_borrowed(v___f_2713_, v_msg_2695_);
lean_dec_ref(v___f_2713_);
lean_inc_ref(v___y_2696_);
v___x_2715_ = lean_apply_3(v___x_162743__overap_2714_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2716_, v___y_2717_, v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2720_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0));
v___x_2723_ = lean_unsigned_to_nat(8u);
v___x_2724_ = lean_unsigned_to_nat(354u);
v___x_2725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2726_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2727_ = l_mkPanicMessageWithDecl(v___x_2726_, v___x_2725_, v___x_2724_, v___x_2723_, v___x_2722_);
return v___x_2727_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2729_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2));
v___x_2730_ = lean_unsigned_to_nat(13u);
v___x_2731_ = lean_unsigned_to_nat(356u);
v___x_2732_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2733_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2734_ = l_mkPanicMessageWithDecl(v___x_2733_, v___x_2732_, v___x_2731_, v___x_2730_, v___x_2729_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t v___x_2735_, lean_object* v_init_2736_, lean_object* v_x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_d_2742_; lean_object* v___y_2743_; 
if (lean_obj_tag(v_x_2737_) == 0)
{
lean_object* v_k_2747_; lean_object* v_l_2748_; lean_object* v_r_2749_; lean_object* v___x_2750_; 
v_k_2747_ = lean_ctor_get(v_x_2737_, 1);
lean_inc(v_k_2747_);
v_l_2748_ = lean_ctor_get(v_x_2737_, 3);
lean_inc(v_l_2748_);
v_r_2749_ = lean_ctor_get(v_x_2737_, 4);
lean_inc(v_r_2749_);
lean_dec_ref_known(v_x_2737_, 5);
v___x_2750_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_2735_, v_init_2736_, v_l_2748_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v_fst_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v_fst_2752_ = lean_ctor_get(v_a_2751_, 0);
lean_inc(v_fst_2752_);
if (lean_obj_tag(v_fst_2752_) == 0)
{
lean_object* v_snd_2753_; lean_object* v_a_2754_; 
lean_dec(v_r_2749_);
lean_dec(v_k_2747_);
v_snd_2753_ = lean_ctor_get(v_a_2751_, 1);
lean_inc(v_snd_2753_);
lean_dec(v_a_2751_);
v_a_2754_ = lean_ctor_get(v_fst_2752_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v_fst_2752_, 1);
v_d_2742_ = v_a_2754_;
v___y_2743_ = v_snd_2753_;
goto v___jp_2741_;
}
else
{
lean_object* v_snd_2755_; lean_object* v_a_2756_; lean_object* v___y_2758_; lean_object* v___y_2762_; lean_object* v___x_2788_; 
v_snd_2755_ = lean_ctor_get(v_a_2751_, 1);
lean_inc(v_snd_2755_);
lean_dec(v_a_2751_);
v_a_2756_ = lean_ctor_get(v_fst_2752_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v_fst_2752_, 1);
lean_inc_ref(v___y_2738_);
v___x_2788_ = l_Lean_Environment_find_x3f(v___y_2738_, v_k_2747_, v___x_2735_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2790_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2789_);
v___y_2762_ = v___x_2790_;
goto v___jp_2761_;
}
else
{
lean_object* v_val_2791_; 
v_val_2791_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_val_2791_);
lean_dec_ref_known(v___x_2788_, 1);
v___y_2762_ = v_val_2791_;
goto v___jp_2761_;
}
v___jp_2757_:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_array_push(v_a_2756_, v___y_2758_);
v_init_2736_ = v___x_2759_;
v_x_2737_ = v_r_2749_;
v___y_2739_ = v_snd_2755_;
goto _start;
}
v___jp_2761_:
{
if (lean_obj_tag(v___y_2762_) == 7)
{
lean_object* v_val_2763_; uint8_t v_isUnsafe_2764_; 
v_val_2763_ = lean_ctor_get(v___y_2762_, 0);
lean_inc_ref(v_val_2763_);
lean_dec_ref_known(v___y_2762_, 1);
v_isUnsafe_2764_ = lean_ctor_get_uint8(v_val_2763_, sizeof(void*)*7 + 1);
if (v_isUnsafe_2764_ == 0)
{
v___y_2758_ = v_val_2763_;
goto v___jp_2757_;
}
else
{
if (v___x_2735_ == 0)
{
uint8_t v_exportUnsafe_2765_; 
v_exportUnsafe_2765_ = lean_ctor_get_uint8(v_snd_2755_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec_ref(v_val_2763_);
lean_dec(v_a_2756_);
v___x_2766_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1);
v___x_2767_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_2766_, v___y_2738_, v_snd_2755_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v_fst_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v_fst_2769_ = lean_ctor_get(v_a_2768_, 0);
lean_inc(v_fst_2769_);
if (lean_obj_tag(v_fst_2769_) == 0)
{
lean_object* v_snd_2770_; lean_object* v_a_2771_; 
lean_dec(v_r_2749_);
v_snd_2770_ = lean_ctor_get(v_a_2768_, 1);
lean_inc(v_snd_2770_);
lean_dec(v_a_2768_);
v_a_2771_ = lean_ctor_get(v_fst_2769_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v_fst_2769_, 1);
v_d_2742_ = v_a_2771_;
v___y_2743_ = v_snd_2770_;
goto v___jp_2741_;
}
else
{
lean_object* v_snd_2772_; lean_object* v_a_2773_; 
v_snd_2772_ = lean_ctor_get(v_a_2768_, 1);
lean_inc(v_snd_2772_);
lean_dec(v_a_2768_);
v_a_2773_ = lean_ctor_get(v_fst_2769_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v_fst_2769_, 1);
v_init_2736_ = v_a_2773_;
v_x_2737_ = v_r_2749_;
v___y_2739_ = v_snd_2772_;
goto _start;
}
}
else
{
lean_dec(v_r_2749_);
return v___x_2767_;
}
}
else
{
v___y_2758_ = v_val_2763_;
goto v___jp_2757_;
}
}
else
{
v___y_2758_ = v_val_2763_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v___y_2762_);
v___x_2775_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3);
v___x_2776_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2775_, v___y_2738_, v_snd_2755_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v_snd_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v_snd_2778_ = lean_ctor_get(v_a_2777_, 1);
lean_inc(v_snd_2778_);
lean_dec(v_a_2777_);
v_init_2736_ = v_a_2756_;
v_x_2737_ = v_r_2749_;
v___y_2739_ = v_snd_2778_;
goto _start;
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2756_);
lean_dec(v_r_2749_);
v_a_2780_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2776_);
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
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_dec(v_r_2749_);
lean_dec(v_k_2747_);
return v___x_2750_;
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v_init_2736_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___y_2739_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
v___jp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_d_2742_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v___y_2743_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object* v___x_2795_, lean_object* v_init_2796_, lean_object* v_x_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v___x_172378__boxed_2801_; lean_object* v_res_2802_; 
v___x_172378__boxed_2801_ = lean_unbox(v___x_2795_);
v_res_2802_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_172378__boxed_2801_, v_init_2796_, v_x_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t v_sz_2803_, size_t v_i_2804_, lean_object* v_bs_2805_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_lt(v_i_2804_, v_sz_2803_);
if (v___x_2806_ == 0)
{
return v_bs_2805_;
}
else
{
lean_object* v_v_2807_; lean_object* v___x_2808_; lean_object* v_bs_x27_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v_v_2807_ = lean_array_uget(v_bs_2805_, v_i_2804_);
v___x_2808_ = lean_unsigned_to_nat(0u);
v_bs_x27_2809_ = lean_array_uset(v_bs_2805_, v_i_2804_, v___x_2808_);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2804_, v___x_2810_);
v___x_2812_ = lean_array_uset(v_bs_x27_2809_, v_i_2804_, v_v_2807_);
v_i_2804_ = v___x_2811_;
v_bs_2805_ = v___x_2812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object* v_sz_2814_, lean_object* v_i_2815_, lean_object* v_bs_2816_){
_start:
{
size_t v_sz_boxed_2817_; size_t v_i_boxed_2818_; lean_object* v_res_2819_; 
v_sz_boxed_2817_ = lean_unbox_usize(v_sz_2814_);
lean_dec(v_sz_2814_);
v_i_boxed_2818_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_boxed_2817_, v_i_boxed_2818_, v_bs_2816_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object* v_a_2820_){
_start:
{
size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_sz_2821_ = lean_array_size(v_a_2820_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_2821_, v___x_2822_, v_a_2820_);
v___x_2824_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_array_mk(v_a_2825_);
v___x_2827_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_2828_, size_t v_sz_2829_, size_t v_i_2830_, lean_object* v_b_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
uint8_t v___x_2835_; 
v___x_2835_ = lean_usize_dec_lt(v_i_2830_, v_sz_2829_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_b_2831_);
lean_ctor_set(v___x_2836_, 1, v___y_2833_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
else
{
lean_object* v_visitedNames_2838_; lean_object* v_visitedLevels_2839_; lean_object* v_visitedExprs_2840_; lean_object* v_visitedConstants_2841_; lean_object* v_noMDataExprs_2842_; uint8_t v_exportMData_2843_; uint8_t v_exportUnsafe_2844_; uint8_t v_ignoreMissing_2845_; lean_object* v_recursorMap_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2865_; 
v_visitedNames_2838_ = lean_ctor_get(v___y_2833_, 0);
v_visitedLevels_2839_ = lean_ctor_get(v___y_2833_, 1);
v_visitedExprs_2840_ = lean_ctor_get(v___y_2833_, 2);
v_visitedConstants_2841_ = lean_ctor_get(v___y_2833_, 3);
v_noMDataExprs_2842_ = lean_ctor_get(v___y_2833_, 4);
v_exportMData_2843_ = lean_ctor_get_uint8(v___y_2833_, sizeof(void*)*6);
v_exportUnsafe_2844_ = lean_ctor_get_uint8(v___y_2833_, sizeof(void*)*6 + 1);
v_ignoreMissing_2845_ = lean_ctor_get_uint8(v___y_2833_, sizeof(void*)*6 + 2);
v_recursorMap_2846_ = lean_ctor_get(v___y_2833_, 5);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___y_2833_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2848_ = v___y_2833_;
v_isShared_2849_ = v_isSharedCheck_2865_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_recursorMap_2846_);
lean_inc(v_noMDataExprs_2842_);
lean_inc(v_visitedConstants_2841_);
lean_inc(v_visitedExprs_2840_);
lean_inc(v_visitedLevels_2839_);
lean_inc(v_visitedNames_2838_);
lean_dec(v___y_2833_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2865_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v_a_2850_; lean_object* v_toConstantVal_2851_; lean_object* v_name_2852_; lean_object* v_type_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v_a_2850_ = lean_array_uget_borrowed(v_as_2828_, v_i_2830_);
v_toConstantVal_2851_ = lean_ctor_get(v_a_2850_, 0);
v_name_2852_ = lean_ctor_get(v_toConstantVal_2851_, 0);
v_type_2853_ = lean_ctor_get(v_toConstantVal_2851_, 2);
v___x_2854_ = lean_box(0);
lean_inc(v_name_2852_);
v___x_2855_ = l_Lean_NameHashSet_insert(v_visitedConstants_2841_, v_name_2852_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 3, v___x_2855_);
v___x_2857_ = v___x_2848_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_visitedNames_2838_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_visitedLevels_2839_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_visitedExprs_2840_);
lean_ctor_set(v_reuseFailAlloc_2864_, 3, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2864_, 4, v_noMDataExprs_2842_);
lean_ctor_set(v_reuseFailAlloc_2864_, 5, v_recursorMap_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*6, v_exportMData_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*6 + 1, v_exportUnsafe_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*6 + 2, v_ignoreMissing_2845_);
v___x_2857_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; 
lean_inc_ref(v_type_2853_);
v___x_2858_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_2853_, v___y_2832_, v___x_2857_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_snd_2860_; size_t v___x_2861_; size_t v___x_2862_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v_snd_2860_ = lean_ctor_get(v_a_2859_, 1);
lean_inc(v_snd_2860_);
lean_dec(v_a_2859_);
v___x_2861_ = ((size_t)1ULL);
v___x_2862_ = lean_usize_add(v_i_2830_, v___x_2861_);
v_i_2830_ = v___x_2862_;
v_b_2831_ = v___x_2854_;
v___y_2833_ = v_snd_2860_;
goto _start;
}
else
{
return v___x_2858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_2866_, lean_object* v_b_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
if (lean_obj_tag(v_as_x27_2866_) == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v_b_2867_);
lean_ctor_set(v___x_2871_, 1, v___y_2869_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
else
{
lean_object* v_head_2873_; lean_object* v_tail_2874_; lean_object* v_rhs_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_head_2873_ = lean_ctor_get(v_as_x27_2866_, 0);
v_tail_2874_ = lean_ctor_get(v_as_x27_2866_, 1);
v_rhs_2875_ = lean_ctor_get(v_head_2873_, 2);
v___x_2876_ = lean_box(0);
lean_inc_ref(v_rhs_2875_);
v___x_2877_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_2875_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_snd_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v_snd_2879_ = lean_ctor_get(v_a_2878_, 1);
lean_inc(v_snd_2879_);
lean_dec(v_a_2878_);
v_as_x27_2866_ = v_tail_2874_;
v_b_2867_ = v___x_2876_;
v___y_2869_ = v_snd_2879_;
goto _start;
}
else
{
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object* v_as_2881_, size_t v_sz_2882_, size_t v_i_2883_, lean_object* v_b_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_usize_dec_lt(v_i_2883_, v_sz_2882_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_b_2884_);
lean_ctor_set(v___x_2889_, 1, v___y_2886_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v_a_2891_; lean_object* v_rules_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2891_ = lean_array_uget_borrowed(v_as_2881_, v_i_2883_);
v_rules_2892_ = lean_ctor_get(v_a_2891_, 6);
v___x_2893_ = lean_box(0);
v___x_2894_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_2892_, v___x_2893_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v_snd_2896_; size_t v___x_2897_; size_t v___x_2898_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v_snd_2896_ = lean_ctor_get(v_a_2895_, 1);
lean_inc(v_snd_2896_);
lean_dec(v_a_2895_);
v___x_2897_ = ((size_t)1ULL);
v___x_2898_ = lean_usize_add(v_i_2883_, v___x_2897_);
v_i_2883_ = v___x_2898_;
v_b_2884_ = v___x_2893_;
v___y_2886_ = v_snd_2896_;
goto _start;
}
else
{
return v___x_2894_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_box(0);
v___x_2901_ = lean_unsigned_to_nat(16u);
v___x_2902_ = lean_mk_array(v___x_2901_, v___x_2900_);
return v___x_2902_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v___x_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v_visitedConstants_2932_; lean_object* v_nat_2933_; uint8_t v___x_2934_; 
v_visitedConstants_2932_ = lean_ctor_get(v_a_2926_, 3);
v_nat_2933_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_2934_ = l_Lean_NameHashSet_contains(v_visitedConstants_2932_, v_nat_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; 
lean_inc_ref(v_a_2925_);
v___x_2935_ = l_Lean_Environment_find_x3f(v_a_2925_, v_nat_2933_, v___x_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
goto v___jp_2928_;
}
else
{
lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2935_, 1);
v___x_2936_ = l_LeanExport_dumpConstant(v_nat_2933_, v_a_2925_, v_a_2926_);
return v___x_2936_;
}
}
else
{
goto v___jp_2928_;
}
v___jp_2928_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_a_2926_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v___y_2952_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v_visitedConstants_2959_; lean_object* v_visitedConstants_2964_; lean_object* v_charOfNat_2965_; uint8_t v___x_2966_; 
v_visitedConstants_2964_ = lean_ctor_get(v_a_2949_, 3);
v_charOfNat_2965_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_2966_ = l_Lean_NameHashSet_contains(v_visitedConstants_2964_, v_charOfNat_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_inc_ref(v_a_2948_);
v___x_2967_ = l_Lean_Environment_find_x3f(v_a_2948_, v_charOfNat_2965_, v___x_2966_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_inc_ref(v_visitedConstants_2964_);
v___y_2957_ = v_a_2948_;
v___y_2958_ = v_a_2949_;
v_visitedConstants_2959_ = v_visitedConstants_2964_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2968_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = l_LeanExport_dumpConstant(v_charOfNat_2965_, v_a_2948_, v_a_2949_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v_snd_2970_; lean_object* v_visitedConstants_2971_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v_snd_2970_ = lean_ctor_get(v_a_2969_, 1);
lean_inc(v_snd_2970_);
lean_dec(v_a_2969_);
v_visitedConstants_2971_ = lean_ctor_get(v_snd_2970_, 3);
lean_inc_ref(v_visitedConstants_2971_);
v___y_2957_ = v_a_2948_;
v___y_2958_ = v_snd_2970_;
v_visitedConstants_2959_ = v_visitedConstants_2971_;
goto v___jp_2956_;
}
else
{
return v___x_2968_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_2964_);
v___y_2957_ = v_a_2948_;
v___y_2958_ = v_a_2949_;
v_visitedConstants_2959_ = v_visitedConstants_2964_;
goto v___jp_2956_;
}
v___jp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v___y_2952_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
v___jp_2956_:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_2961_ = l_Lean_NameHashSet_contains(v_visitedConstants_2959_, v___x_2960_);
lean_dec_ref(v_visitedConstants_2959_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; 
lean_inc_ref(v___y_2957_);
v___x_2962_ = l_Lean_Environment_find_x3f(v___y_2957_, v___x_2960_, v___x_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
v___y_2952_ = v___y_2958_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2963_; 
lean_dec_ref_known(v___x_2962_, 1);
v___x_2963_ = l_LeanExport_dumpConstant(v___x_2960_, v___y_2957_, v___y_2958_);
return v___x_2963_;
}
}
else
{
v___y_2952_ = v___y_2958_;
goto v___jp_2951_;
}
}
}
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2982_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_2983_ = lean_unsigned_to_nat(29u);
v___x_2984_ = lean_unsigned_to_nat(177u);
v___x_2985_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_2986_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2987_ = l_mkPanicMessageWithDecl(v___x_2986_, v___x_2985_, v___x_2984_, v___x_2983_, v___x_2982_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_visitedNames_2992_; lean_object* v_visitedLevels_2993_; lean_object* v_visitedExprs_2994_; lean_object* v_visitedConstants_2995_; lean_object* v_noMDataExprs_2996_; uint8_t v_exportMData_2997_; uint8_t v_exportUnsafe_2998_; uint8_t v_ignoreMissing_2999_; lean_object* v_recursorMap_3000_; lean_object* v___x_3001_; 
v_visitedNames_2992_ = lean_ctor_get(v_a_2990_, 0);
v_visitedLevels_2993_ = lean_ctor_get(v_a_2990_, 1);
v_visitedExprs_2994_ = lean_ctor_get(v_a_2990_, 2);
v_visitedConstants_2995_ = lean_ctor_get(v_a_2990_, 3);
v_noMDataExprs_2996_ = lean_ctor_get(v_a_2990_, 4);
v_exportMData_2997_ = lean_ctor_get_uint8(v_a_2990_, sizeof(void*)*6);
v_exportUnsafe_2998_ = lean_ctor_get_uint8(v_a_2990_, sizeof(void*)*6 + 1);
v_ignoreMissing_2999_ = lean_ctor_get_uint8(v_a_2990_, sizeof(void*)*6 + 2);
v_recursorMap_3000_ = lean_ctor_get(v_a_2990_, 5);
v___x_3001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_2994_, v_e_2988_);
if (lean_obj_tag(v___x_3001_) == 1)
{
lean_object* v_val_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_e_2988_);
v_val_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_val_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3010_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_val_3002_);
lean_ctor_set(v___x_3006_, 1, v_a_2990_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set_tag(v___x_3004_, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3006_);
v___x_3008_ = v___x_3004_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
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
lean_object* v___x_3011_; lean_object* v_fst_3013_; lean_object* v_visitedNames_3014_; lean_object* v_visitedLevels_3015_; lean_object* v_visitedExprs_3016_; lean_object* v_visitedConstants_3017_; lean_object* v_noMDataExprs_3018_; uint8_t v_exportMData_3019_; uint8_t v_exportUnsafe_3020_; uint8_t v_ignoreMissing_3021_; lean_object* v_recursorMap_3022_; lean_object* v_fst_3049_; lean_object* v_snd_3050_; 
lean_dec(v___x_3001_);
v___x_3011_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_2988_))
{
case 0:
{
lean_object* v_deBruijnIndex_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_inc(v_recursorMap_3000_);
lean_inc_ref(v_noMDataExprs_2996_);
lean_inc_ref(v_visitedConstants_2995_);
lean_inc_ref(v_visitedExprs_2994_);
lean_inc_ref(v_visitedLevels_2993_);
lean_inc_ref(v_visitedNames_2992_);
lean_dec_ref(v_a_2990_);
v_deBruijnIndex_3060_ = lean_ctor_get(v_e_2988_, 0);
v___x_3061_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3060_);
v___x_3062_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3060_);
v___x_3063_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3061_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_Json_mkObj(v___x_3066_);
lean_dec_ref_known(v___x_3066_, 2);
v_fst_3013_ = v___x_3067_;
v_visitedNames_3014_ = v_visitedNames_2992_;
v_visitedLevels_3015_ = v_visitedLevels_2993_;
v_visitedExprs_3016_ = v_visitedExprs_2994_;
v_visitedConstants_3017_ = v_visitedConstants_2995_;
v_noMDataExprs_3018_ = v_noMDataExprs_2996_;
v_exportMData_3019_ = v_exportMData_2997_;
v_exportUnsafe_3020_ = v_exportUnsafe_2998_;
v_ignoreMissing_3021_ = v_ignoreMissing_2999_;
v_recursorMap_3022_ = v_recursorMap_3000_;
goto v___jp_3012_;
}
case 3:
{
lean_object* v_u_3068_; lean_object* v___x_3069_; 
v_u_3068_ = lean_ctor_get(v_e_2988_, 0);
lean_inc(v_u_3068_);
v___x_3069_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3068_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3091_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3091_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3091_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_fst_3074_; lean_object* v_snd_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3090_; 
v_fst_3074_ = lean_ctor_get(v_a_3070_, 0);
v_snd_3075_ = lean_ctor_get(v_a_3070_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_a_3070_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3077_ = v_a_3070_;
v_isShared_3078_ = v_isSharedCheck_3090_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_snd_3075_);
lean_inc(v_fst_3074_);
lean_dec(v_a_3070_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3090_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3079_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3080_ = l_Lean_JsonNumber_fromNat(v_fst_3074_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set_tag(v___x_3072_, 2);
lean_ctor_set(v___x_3072_, 0, v___x_3080_);
v___x_3082_ = v___x_3072_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3082_);
lean_ctor_set(v___x_3077_, 0, v___x_3079_);
v___x_3084_ = v___x_3077_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_box(0);
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3084_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = l_Lean_Json_mkObj(v___x_3086_);
lean_dec_ref_known(v___x_3086_, 2);
v_fst_3049_ = v___x_3087_;
v_snd_3050_ = v_snd_3075_;
goto v___jp_3048_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 1);
return v___x_3069_;
}
}
case 4:
{
lean_object* v_declName_3092_; lean_object* v_us_3093_; lean_object* v___x_3094_; 
v_declName_3092_ = lean_ctor_get(v_e_2988_, 0);
v_us_3093_ = lean_ctor_get(v_e_2988_, 1);
lean_inc(v_declName_3092_);
v___x_3094_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3092_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3142_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3142_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3142_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3141_; 
v_fst_3099_ = lean_ctor_get(v_a_3095_, 0);
v_snd_3100_ = lean_ctor_get(v_a_3095_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_a_3095_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3102_ = v_a_3095_;
v_isShared_3103_ = v_isSharedCheck_3141_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_snd_3100_);
lean_inc(v_fst_3099_);
lean_dec(v_a_3095_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3141_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_box(0);
lean_inc(v_us_3093_);
v___x_3105_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3093_, v___x_3104_, v_a_2989_, v_snd_3100_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v_fst_3107_; lean_object* v_snd_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3132_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v_fst_3107_ = lean_ctor_get(v_a_3106_, 0);
v_snd_3108_ = lean_ctor_get(v_a_3106_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3110_ = v_a_3106_;
v_isShared_3111_ = v_isSharedCheck_3132_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_snd_3108_);
lean_inc(v_fst_3107_);
lean_dec(v_a_3106_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3132_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3112_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3114_ = l_Lean_JsonNumber_fromNat(v_fst_3099_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 2);
lean_ctor_set(v___x_3097_, 0, v___x_3114_);
v___x_3116_ = v___x_3097_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3118_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v___x_3116_);
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3118_ = v___x_3110_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3120_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3107_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v___x_3120_);
lean_ctor_set(v___x_3102_, 0, v___x_3119_);
v___x_3122_ = v___x_3102_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___x_3104_);
v___x_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3118_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = l_Lean_Json_mkObj(v___x_3124_);
lean_dec_ref_known(v___x_3124_, 2);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3112_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3104_);
v___x_3128_ = l_Lean_Json_mkObj(v___x_3127_);
lean_dec_ref_known(v___x_3127_, 2);
v_fst_3049_ = v___x_3128_;
v_snd_3050_ = v_snd_3108_;
goto v___jp_3048_;
}
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_del_object(v___x_3102_);
lean_dec(v_fst_3099_);
lean_del_object(v___x_3097_);
lean_dec_ref_known(v_e_2988_, 2);
v_a_3133_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3105_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3105_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 2);
return v___x_3094_;
}
}
case 5:
{
lean_object* v_fn_3143_; lean_object* v_arg_3144_; lean_object* v___x_3145_; 
v_fn_3143_ = lean_ctor_get(v_e_2988_, 0);
v_arg_3144_ = lean_ctor_get(v_e_2988_, 1);
lean_inc_ref(v_fn_3143_);
v___x_3145_ = l_LeanExport_dumpExprAux(v_fn_3143_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3192_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3192_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3192_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v_snd_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3191_; 
v_fst_3150_ = lean_ctor_get(v_a_3146_, 0);
v_snd_3151_ = lean_ctor_get(v_a_3146_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_3146_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3153_ = v_a_3146_;
v_isShared_3154_ = v_isSharedCheck_3191_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_snd_3151_);
lean_inc(v_fst_3150_);
lean_dec(v_a_3146_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3191_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; 
lean_inc_ref(v_arg_3144_);
v___x_3155_ = l_LeanExport_dumpExprAux(v_arg_3144_, v_a_2989_, v_snd_3151_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3190_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3190_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3190_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_fst_3160_; lean_object* v_snd_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3189_; 
v_fst_3160_ = lean_ctor_get(v_a_3156_, 0);
v_snd_3161_ = lean_ctor_get(v_a_3156_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_a_3156_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3163_ = v_a_3156_;
v_isShared_3164_ = v_isSharedCheck_3189_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snd_3161_);
lean_inc(v_fst_3160_);
lean_dec(v_a_3156_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3189_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3165_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3166_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3167_ = l_Lean_JsonNumber_fromNat(v_fst_3150_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 2);
lean_ctor_set(v___x_3158_, 0, v___x_3167_);
v___x_3169_ = v___x_3158_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3171_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3169_);
lean_ctor_set(v___x_3163_, 0, v___x_3166_);
v___x_3171_ = v___x_3163_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3172_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3173_ = l_Lean_JsonNumber_fromNat(v_fst_3160_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set_tag(v___x_3148_, 2);
lean_ctor_set(v___x_3148_, 0, v___x_3173_);
v___x_3175_ = v___x_3148_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3177_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3175_);
lean_ctor_set(v___x_3153_, 0, v___x_3172_);
v___x_3177_ = v___x_3153_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3171_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l_Lean_Json_mkObj(v___x_3180_);
lean_dec_ref_known(v___x_3180_, 2);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3165_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
lean_ctor_set(v___x_3183_, 1, v___x_3178_);
v___x_3184_ = l_Lean_Json_mkObj(v___x_3183_);
lean_dec_ref_known(v___x_3183_, 2);
v_fst_3049_ = v___x_3184_;
v_snd_3050_ = v_snd_3161_;
goto v___jp_3048_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3153_);
lean_dec(v_fst_3150_);
lean_del_object(v___x_3148_);
lean_dec_ref_known(v_e_2988_, 2);
return v___x_3155_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 2);
return v___x_3145_;
}
}
case 6:
{
lean_object* v_binderName_3193_; lean_object* v_binderType_3194_; lean_object* v_body_3195_; uint8_t v_binderInfo_3196_; lean_object* v___x_3197_; 
v_binderName_3193_ = lean_ctor_get(v_e_2988_, 0);
v_binderType_3194_ = lean_ctor_get(v_e_2988_, 1);
v_body_3195_ = lean_ctor_get(v_e_2988_, 2);
v_binderInfo_3196_ = lean_ctor_get_uint8(v_e_2988_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3193_);
v___x_3197_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3193_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3269_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3269_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3269_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3268_; 
v_fst_3202_ = lean_ctor_get(v_a_3198_, 0);
v_snd_3203_ = lean_ctor_get(v_a_3198_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3205_ = v_a_3198_;
v_isShared_3206_ = v_isSharedCheck_3268_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_snd_3203_);
lean_inc(v_fst_3202_);
lean_dec(v_a_3198_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3268_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; 
lean_inc_ref(v_binderType_3194_);
v___x_3207_ = l_LeanExport_dumpExprAux(v_binderType_3194_, v_a_2989_, v_snd_3203_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3267_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3267_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3267_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_fst_3212_; lean_object* v_snd_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3266_; 
v_fst_3212_ = lean_ctor_get(v_a_3208_, 0);
v_snd_3213_ = lean_ctor_get(v_a_3208_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_a_3208_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3215_ = v_a_3208_;
v_isShared_3216_ = v_isSharedCheck_3266_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_snd_3213_);
lean_inc(v_fst_3212_);
lean_dec(v_a_3208_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3266_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; 
lean_inc_ref(v_body_3195_);
v___x_3217_ = l_LeanExport_dumpExprAux(v_body_3195_, v_a_2989_, v_snd_3213_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3265_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3265_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3265_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v_fst_3222_; lean_object* v_snd_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3264_; 
v_fst_3222_ = lean_ctor_get(v_a_3218_, 0);
v_snd_3223_ = lean_ctor_get(v_a_3218_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3218_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3225_ = v_a_3218_;
v_isShared_3226_ = v_isSharedCheck_3264_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_snd_3223_);
lean_inc(v_fst_3222_);
lean_dec(v_a_3218_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3264_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3227_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3229_ = l_Lean_JsonNumber_fromNat(v_fst_3202_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 2);
lean_ctor_set(v___x_3220_, 0, v___x_3229_);
v___x_3231_ = v___x_3220_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v___x_3231_);
lean_ctor_set(v___x_3225_, 0, v___x_3228_);
v___x_3233_ = v___x_3225_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3234_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3235_ = l_Lean_JsonNumber_fromNat(v_fst_3212_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 2);
lean_ctor_set(v___x_3210_, 0, v___x_3235_);
v___x_3237_ = v___x_3210_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3239_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v___x_3237_);
lean_ctor_set(v___x_3215_, 0, v___x_3234_);
v___x_3239_ = v___x_3215_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3240_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3241_ = l_Lean_JsonNumber_fromNat(v_fst_3222_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 2);
lean_ctor_set(v___x_3200_, 0, v___x_3241_);
v___x_3243_ = v___x_3200_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v___x_3243_);
lean_ctor_set(v___x_3205_, 0, v___x_3240_);
v___x_3245_ = v___x_3205_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3246_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3247_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3196_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_box(0);
v___x_3250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3245_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3239_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3233_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_Json_mkObj(v___x_3253_);
lean_dec_ref_known(v___x_3253_, 2);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3227_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v___x_3249_);
v___x_3257_ = l_Lean_Json_mkObj(v___x_3256_);
lean_dec_ref_known(v___x_3256_, 2);
v_fst_3049_ = v___x_3257_;
v_snd_3050_ = v_snd_3223_;
goto v___jp_3048_;
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
lean_del_object(v___x_3215_);
lean_dec(v_fst_3212_);
lean_del_object(v___x_3210_);
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_del_object(v___x_3200_);
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3217_;
}
}
}
}
else
{
lean_del_object(v___x_3205_);
lean_dec(v_fst_3202_);
lean_del_object(v___x_3200_);
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3207_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3197_;
}
}
case 7:
{
lean_object* v_binderName_3270_; lean_object* v_binderType_3271_; lean_object* v_body_3272_; uint8_t v_binderInfo_3273_; lean_object* v___x_3274_; 
v_binderName_3270_ = lean_ctor_get(v_e_2988_, 0);
v_binderType_3271_ = lean_ctor_get(v_e_2988_, 1);
v_body_3272_ = lean_ctor_get(v_e_2988_, 2);
v_binderInfo_3273_ = lean_ctor_get_uint8(v_e_2988_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3270_);
v___x_3274_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3270_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3346_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3346_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3346_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_fst_3279_; lean_object* v_snd_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3345_; 
v_fst_3279_ = lean_ctor_get(v_a_3275_, 0);
v_snd_3280_ = lean_ctor_get(v_a_3275_, 1);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_a_3275_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3282_ = v_a_3275_;
v_isShared_3283_ = v_isSharedCheck_3345_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_snd_3280_);
lean_inc(v_fst_3279_);
lean_dec(v_a_3275_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3345_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; 
lean_inc_ref(v_binderType_3271_);
v___x_3284_ = l_LeanExport_dumpExprAux(v_binderType_3271_, v_a_2989_, v_snd_3280_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3344_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3344_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3344_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v_fst_3289_; lean_object* v_snd_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3343_; 
v_fst_3289_ = lean_ctor_get(v_a_3285_, 0);
v_snd_3290_ = lean_ctor_get(v_a_3285_, 1);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_a_3285_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3292_ = v_a_3285_;
v_isShared_3293_ = v_isSharedCheck_3343_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_snd_3290_);
lean_inc(v_fst_3289_);
lean_dec(v_a_3285_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3343_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; 
lean_inc_ref(v_body_3272_);
v___x_3294_ = l_LeanExport_dumpExprAux(v_body_3272_, v_a_2989_, v_snd_3290_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3342_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3342_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3342_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3341_; 
v_fst_3299_ = lean_ctor_get(v_a_3295_, 0);
v_snd_3300_ = lean_ctor_get(v_a_3295_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_a_3295_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3302_ = v_a_3295_;
v_isShared_3303_ = v_isSharedCheck_3341_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_snd_3300_);
lean_inc(v_fst_3299_);
lean_dec(v_a_3295_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3341_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3304_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3306_ = l_Lean_JsonNumber_fromNat(v_fst_3279_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 2);
lean_ctor_set(v___x_3297_, 0, v___x_3306_);
v___x_3308_ = v___x_3297_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 1, v___x_3308_);
lean_ctor_set(v___x_3302_, 0, v___x_3305_);
v___x_3310_ = v___x_3302_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v___x_3311_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3312_ = l_Lean_JsonNumber_fromNat(v_fst_3289_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 2);
lean_ctor_set(v___x_3287_, 0, v___x_3312_);
v___x_3314_ = v___x_3287_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 1, v___x_3314_);
lean_ctor_set(v___x_3292_, 0, v___x_3311_);
v___x_3316_ = v___x_3292_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3317_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3318_ = l_Lean_JsonNumber_fromNat(v_fst_3299_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 2);
lean_ctor_set(v___x_3277_, 0, v___x_3318_);
v___x_3320_ = v___x_3277_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
lean_object* v___x_3322_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 1, v___x_3320_);
lean_ctor_set(v___x_3282_, 0, v___x_3317_);
v___x_3322_ = v___x_3282_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3320_);
v___x_3322_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3323_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3324_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3273_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3322_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3316_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3310_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_Json_mkObj(v___x_3330_);
lean_dec_ref_known(v___x_3330_, 2);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3304_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3326_);
v___x_3334_ = l_Lean_Json_mkObj(v___x_3333_);
lean_dec_ref_known(v___x_3333_, 2);
v_fst_3049_ = v___x_3334_;
v_snd_3050_ = v_snd_3300_;
goto v___jp_3048_;
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
lean_del_object(v___x_3292_);
lean_dec(v_fst_3289_);
lean_del_object(v___x_3287_);
lean_del_object(v___x_3282_);
lean_dec(v_fst_3279_);
lean_del_object(v___x_3277_);
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3294_;
}
}
}
}
else
{
lean_del_object(v___x_3282_);
lean_dec(v_fst_3279_);
lean_del_object(v___x_3277_);
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3284_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3274_;
}
}
case 8:
{
lean_object* v_declName_3347_; lean_object* v_type_3348_; lean_object* v_value_3349_; lean_object* v_body_3350_; uint8_t v_nondep_3351_; lean_object* v___x_3352_; 
v_declName_3347_ = lean_ctor_get(v_e_2988_, 0);
v_type_3348_ = lean_ctor_get(v_e_2988_, 1);
v_value_3349_ = lean_ctor_get(v_e_2988_, 2);
v_body_3350_ = lean_ctor_get(v_e_2988_, 3);
v_nondep_3351_ = lean_ctor_get_uint8(v_e_2988_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3347_);
v___x_3352_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3347_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3445_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3445_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3445_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3444_; 
v_fst_3357_ = lean_ctor_get(v_a_3353_, 0);
v_snd_3358_ = lean_ctor_get(v_a_3353_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_a_3353_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3360_ = v_a_3353_;
v_isShared_3361_ = v_isSharedCheck_3444_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_a_3353_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3444_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; 
lean_inc_ref(v_type_3348_);
v___x_3362_ = l_LeanExport_dumpExprAux(v_type_3348_, v_a_2989_, v_snd_3358_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3443_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3443_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3443_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3442_; 
v_fst_3367_ = lean_ctor_get(v_a_3363_, 0);
v_snd_3368_ = lean_ctor_get(v_a_3363_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_a_3363_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3370_ = v_a_3363_;
v_isShared_3371_ = v_isSharedCheck_3442_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_inc(v_fst_3367_);
lean_dec(v_a_3363_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3442_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; 
lean_inc_ref(v_value_3349_);
v___x_3372_ = l_LeanExport_dumpExprAux(v_value_3349_, v_a_2989_, v_snd_3368_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3441_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3441_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3441_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_fst_3377_; lean_object* v_snd_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3440_; 
v_fst_3377_ = lean_ctor_get(v_a_3373_, 0);
v_snd_3378_ = lean_ctor_get(v_a_3373_, 1);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_a_3373_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3380_ = v_a_3373_;
v_isShared_3381_ = v_isSharedCheck_3440_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_snd_3378_);
lean_inc(v_fst_3377_);
lean_dec(v_a_3373_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3440_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; 
lean_inc_ref(v_body_3350_);
v___x_3382_ = l_LeanExport_dumpExprAux(v_body_3350_, v_a_2989_, v_snd_3378_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3439_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3439_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3439_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v_fst_3387_; lean_object* v_snd_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3438_; 
v_fst_3387_ = lean_ctor_get(v_a_3383_, 0);
v_snd_3388_ = lean_ctor_get(v_a_3383_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3390_ = v_a_3383_;
v_isShared_3391_ = v_isSharedCheck_3438_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_snd_3388_);
lean_inc(v_fst_3387_);
lean_dec(v_a_3383_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3438_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3392_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3394_ = l_Lean_JsonNumber_fromNat(v_fst_3357_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 2);
lean_ctor_set(v___x_3385_, 0, v___x_3394_);
v___x_3396_ = v___x_3385_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v___x_3396_);
lean_ctor_set(v___x_3390_, 0, v___x_3393_);
v___x_3398_ = v___x_3390_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3393_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3399_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3400_ = l_Lean_JsonNumber_fromNat(v_fst_3367_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 2);
lean_ctor_set(v___x_3375_, 0, v___x_3400_);
v___x_3402_ = v___x_3375_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3404_; 
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 1, v___x_3402_);
lean_ctor_set(v___x_3380_, 0, v___x_3399_);
v___x_3404_ = v___x_3380_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3405_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3406_ = l_Lean_JsonNumber_fromNat(v_fst_3377_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 2);
lean_ctor_set(v___x_3365_, 0, v___x_3406_);
v___x_3408_ = v___x_3365_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v___x_3408_);
lean_ctor_set(v___x_3370_, 0, v___x_3405_);
v___x_3410_ = v___x_3370_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3412_ = l_Lean_JsonNumber_fromNat(v_fst_3387_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 2);
lean_ctor_set(v___x_3355_, 0, v___x_3412_);
v___x_3414_ = v___x_3355_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3416_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v___x_3414_);
lean_ctor_set(v___x_3360_, 0, v___x_3411_);
v___x_3416_ = v___x_3360_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3417_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3418_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3418_, 0, v_nondep_3351_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_box(0);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3416_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3410_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3404_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3398_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_Json_mkObj(v___x_3425_);
lean_dec_ref_known(v___x_3425_, 2);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3392_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___x_3420_);
v___x_3429_ = l_Lean_Json_mkObj(v___x_3428_);
lean_dec_ref_known(v___x_3428_, 2);
v_fst_3049_ = v___x_3429_;
v_snd_3050_ = v_snd_3388_;
goto v___jp_3048_;
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
lean_del_object(v___x_3380_);
lean_dec(v_fst_3377_);
lean_del_object(v___x_3375_);
lean_del_object(v___x_3370_);
lean_dec(v_fst_3367_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3360_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec_ref_known(v_e_2988_, 4);
return v___x_3382_;
}
}
}
}
else
{
lean_del_object(v___x_3370_);
lean_dec(v_fst_3367_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3360_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec_ref_known(v_e_2988_, 4);
return v___x_3372_;
}
}
}
}
else
{
lean_del_object(v___x_3360_);
lean_dec(v_fst_3357_);
lean_del_object(v___x_3355_);
lean_dec_ref_known(v_e_2988_, 4);
return v___x_3362_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 4);
return v___x_3352_;
}
}
case 9:
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v_e_2988_, 0);
lean_inc_ref(v_a_3446_);
if (lean_obj_tag(v_a_3446_) == 0)
{
lean_object* v_val_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3478_; 
v_val_3447_ = lean_ctor_get(v_a_3446_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3449_ = v_a_3446_;
v_isShared_3450_ = v_isSharedCheck_3478_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_val_3447_);
lean_dec(v_a_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3478_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; 
v___x_3451_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v_snd_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3468_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v_snd_3453_ = lean_ctor_get(v_a_3452_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v_a_3452_, 0);
lean_dec(v_unused_3469_);
v___x_3455_ = v_a_3452_;
v_isShared_3456_ = v_isSharedCheck_3468_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snd_3453_);
lean_dec(v_a_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3468_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3457_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3458_ = l_Nat_reprFast(v_val_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 3);
lean_ctor_set(v___x_3449_, 0, v___x_3458_);
v___x_3460_ = v___x_3449_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 1, v___x_3460_);
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3462_ = v___x_3455_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Lean_Json_mkObj(v___x_3464_);
lean_dec_ref_known(v___x_3464_, 2);
v_fst_3049_ = v___x_3465_;
v_snd_3050_ = v_snd_3453_;
goto v___jp_3048_;
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref_known(v_e_2988_, 1);
v_a_3470_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3451_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3451_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
else
{
lean_object* v_val_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3509_; 
v_val_3479_ = lean_ctor_get(v_a_3446_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3481_ = v_a_3446_;
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_val_3479_);
lean_dec(v_a_3446_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; 
v___x_3483_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v_snd_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3499_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v_snd_3485_ = lean_ctor_get(v_a_3484_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3484_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; 
v_unused_3500_ = lean_ctor_get(v_a_3484_, 0);
lean_dec(v_unused_3500_);
v___x_3487_ = v_a_3484_;
v_isShared_3488_ = v_isSharedCheck_3499_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_snd_3485_);
lean_dec(v_a_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3499_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 3);
v___x_3491_ = v___x_3481_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_val_3479_);
v___x_3491_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3491_);
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3493_ = v___x_3487_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_box(0);
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_Json_mkObj(v___x_3495_);
lean_dec_ref_known(v___x_3495_, 2);
v_fst_3049_ = v___x_3496_;
v_snd_3050_ = v_snd_3485_;
goto v___jp_3048_;
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_del_object(v___x_3481_);
lean_dec_ref(v_val_3479_);
lean_dec_ref_known(v_e_2988_, 1);
v_a_3501_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3483_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3483_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3510_; lean_object* v_expr_3511_; lean_object* v___x_3512_; 
v_data_3510_ = lean_ctor_get(v_e_2988_, 0);
v_expr_3511_ = lean_ctor_get(v_e_2988_, 1);
lean_inc_ref(v_expr_3511_);
v___x_3512_ = l_LeanExport_dumpExprAux(v_expr_3511_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3542_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3542_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3542_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_fst_3517_; lean_object* v_snd_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3541_; 
v_fst_3517_ = lean_ctor_get(v_a_3513_, 0);
v_snd_3518_ = lean_ctor_get(v_a_3513_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_a_3513_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3520_ = v_a_3513_;
v_isShared_3521_ = v_isSharedCheck_3541_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_snd_3518_);
lean_inc(v_fst_3517_);
lean_dec(v_a_3513_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3541_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3522_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3523_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3510_);
v___x_3524_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3510_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 1, v___x_3524_);
lean_ctor_set(v___x_3520_, 0, v___x_3523_);
v___x_3526_ = v___x_3520_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3527_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3528_ = l_Lean_JsonNumber_fromNat(v_fst_3517_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set_tag(v___x_3515_, 2);
lean_ctor_set(v___x_3515_, 0, v___x_3528_);
v___x_3530_ = v___x_3515_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3527_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = lean_box(0);
v___x_3533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3526_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_Lean_Json_mkObj(v___x_3534_);
lean_dec_ref_known(v___x_3534_, 2);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3522_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v___x_3532_);
v___x_3538_ = l_Lean_Json_mkObj(v___x_3537_);
lean_dec_ref_known(v___x_3537_, 2);
v_fst_3049_ = v___x_3538_;
v_snd_3050_ = v_snd_3518_;
goto v___jp_3048_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 2);
return v___x_3512_;
}
}
case 11:
{
lean_object* v_typeName_3543_; lean_object* v_idx_3544_; lean_object* v_struct_3545_; lean_object* v___x_3546_; 
v_typeName_3543_ = lean_ctor_get(v_e_2988_, 0);
v_idx_3544_ = lean_ctor_get(v_e_2988_, 1);
v_struct_3545_ = lean_ctor_get(v_e_2988_, 2);
lean_inc(v_typeName_3543_);
v___x_3546_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3543_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3598_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3598_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3598_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_fst_3551_; lean_object* v_snd_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3597_; 
v_fst_3551_ = lean_ctor_get(v_a_3547_, 0);
v_snd_3552_ = lean_ctor_get(v_a_3547_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3547_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3554_ = v_a_3547_;
v_isShared_3555_ = v_isSharedCheck_3597_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_snd_3552_);
lean_inc(v_fst_3551_);
lean_dec(v_a_3547_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3597_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; 
lean_inc_ref(v_struct_3545_);
v___x_3556_ = l_LeanExport_dumpExprAux(v_struct_3545_, v_a_2989_, v_snd_3552_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3596_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3596_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3596_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v_fst_3561_; lean_object* v_snd_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3595_; 
v_fst_3561_ = lean_ctor_get(v_a_3557_, 0);
v_snd_3562_ = lean_ctor_get(v_a_3557_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3557_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3564_ = v_a_3557_;
v_isShared_3565_ = v_isSharedCheck_3595_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_snd_3562_);
lean_inc(v_fst_3561_);
lean_dec(v_a_3557_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3595_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3566_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3567_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3568_ = l_Lean_JsonNumber_fromNat(v_fst_3551_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 2);
lean_ctor_set(v___x_3559_, 0, v___x_3568_);
v___x_3570_ = v___x_3559_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3572_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3570_);
lean_ctor_set(v___x_3564_, 0, v___x_3567_);
v___x_3572_ = v___x_3564_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3573_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3544_);
v___x_3574_ = l_Lean_JsonNumber_fromNat(v_idx_3544_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set_tag(v___x_3549_, 2);
lean_ctor_set(v___x_3549_, 0, v___x_3574_);
v___x_3576_ = v___x_3549_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v___x_3576_);
lean_ctor_set(v___x_3554_, 0, v___x_3573_);
v___x_3578_ = v___x_3554_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3579_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3580_ = l_Lean_JsonNumber_fromNat(v_fst_3561_);
v___x_3581_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3579_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_box(0);
v___x_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3578_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3572_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = l_Lean_Json_mkObj(v___x_3586_);
lean_dec_ref_known(v___x_3586_, 2);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3566_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___x_3583_);
v___x_3590_ = l_Lean_Json_mkObj(v___x_3589_);
lean_dec_ref_known(v___x_3589_, 2);
v_fst_3049_ = v___x_3590_;
v_snd_3050_ = v_snd_3562_;
goto v___jp_3048_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3554_);
lean_dec(v_fst_3551_);
lean_del_object(v___x_3549_);
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3556_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2988_, 3);
return v___x_3546_;
}
}
default: 
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3600_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3599_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_fst_3602_; lean_object* v_snd_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v_fst_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_fst_3602_);
v_snd_3603_ = lean_ctor_get(v_a_3601_, 1);
lean_inc(v_snd_3603_);
lean_dec(v_a_3601_);
v_fst_3049_ = v_fst_3602_;
v_snd_3050_ = v_snd_3603_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref(v_e_2988_);
v_a_3604_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3600_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3600_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
v___jp_3012_:
{
lean_object* v_size_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_size_3023_ = lean_ctor_get(v_visitedExprs_3016_, 0);
lean_inc_n(v_size_3023_, 2);
v___x_3024_ = l_Lean_JsonNumber_fromNat(v_size_3023_);
v___x_3025_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
v___x_3026_ = l_Lean_Json_setObjVal_x21(v_fst_3013_, v___x_3011_, v___x_3025_);
v___x_3027_ = l_Lean_Json_compress(v___x_3026_);
v___x_3028_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3038_; 
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; 
v_unused_3039_ = lean_ctor_get(v___x_3028_, 0);
lean_dec(v_unused_3039_);
v___x_3030_ = v___x_3028_;
v_isShared_3031_ = v_isSharedCheck_3038_;
goto v_resetjp_3029_;
}
else
{
lean_dec(v___x_3028_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3038_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_inc(v_size_3023_);
v___x_3032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3016_, v_e_2988_, v_size_3023_);
v___x_3033_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3033_, 0, v_visitedNames_3014_);
lean_ctor_set(v___x_3033_, 1, v_visitedLevels_3015_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
lean_ctor_set(v___x_3033_, 3, v_visitedConstants_3017_);
lean_ctor_set(v___x_3033_, 4, v_noMDataExprs_3018_);
lean_ctor_set(v___x_3033_, 5, v_recursorMap_3022_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*6, v_exportMData_3019_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*6 + 1, v_exportUnsafe_3020_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*6 + 2, v_ignoreMissing_3021_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_size_3023_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3034_);
v___x_3036_ = v___x_3030_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec(v_size_3023_);
lean_dec(v_recursorMap_3022_);
lean_dec_ref(v_noMDataExprs_3018_);
lean_dec_ref(v_visitedConstants_3017_);
lean_dec_ref(v_visitedExprs_3016_);
lean_dec_ref(v_visitedLevels_3015_);
lean_dec_ref(v_visitedNames_3014_);
lean_dec_ref(v_e_2988_);
v_a_3040_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3028_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3028_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
v___jp_3048_:
{
lean_object* v_visitedNames_3051_; lean_object* v_visitedLevels_3052_; lean_object* v_visitedExprs_3053_; lean_object* v_visitedConstants_3054_; lean_object* v_noMDataExprs_3055_; uint8_t v_exportMData_3056_; uint8_t v_exportUnsafe_3057_; uint8_t v_ignoreMissing_3058_; lean_object* v_recursorMap_3059_; 
v_visitedNames_3051_ = lean_ctor_get(v_snd_3050_, 0);
lean_inc_ref(v_visitedNames_3051_);
v_visitedLevels_3052_ = lean_ctor_get(v_snd_3050_, 1);
lean_inc_ref(v_visitedLevels_3052_);
v_visitedExprs_3053_ = lean_ctor_get(v_snd_3050_, 2);
lean_inc_ref(v_visitedExprs_3053_);
v_visitedConstants_3054_ = lean_ctor_get(v_snd_3050_, 3);
lean_inc_ref(v_visitedConstants_3054_);
v_noMDataExprs_3055_ = lean_ctor_get(v_snd_3050_, 4);
lean_inc_ref(v_noMDataExprs_3055_);
v_exportMData_3056_ = lean_ctor_get_uint8(v_snd_3050_, sizeof(void*)*6);
v_exportUnsafe_3057_ = lean_ctor_get_uint8(v_snd_3050_, sizeof(void*)*6 + 1);
v_ignoreMissing_3058_ = lean_ctor_get_uint8(v_snd_3050_, sizeof(void*)*6 + 2);
v_recursorMap_3059_ = lean_ctor_get(v_snd_3050_, 5);
lean_inc(v_recursorMap_3059_);
lean_dec_ref(v_snd_3050_);
v_fst_3013_ = v_fst_3049_;
v_visitedNames_3014_ = v_visitedNames_3051_;
v_visitedLevels_3015_ = v_visitedLevels_3052_;
v_visitedExprs_3016_ = v_visitedExprs_3053_;
v_visitedConstants_3017_ = v_visitedConstants_3054_;
v_noMDataExprs_3018_ = v_noMDataExprs_3055_;
v_exportMData_3019_ = v_exportMData_3056_;
v_exportUnsafe_3020_ = v_exportUnsafe_3057_;
v_ignoreMissing_3021_ = v_ignoreMissing_3058_;
v_recursorMap_3022_ = v_recursorMap_3059_;
goto v___jp_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
uint8_t v_exportMData_3616_; 
v_exportMData_3616_ = lean_ctor_get_uint8(v_a_3614_, sizeof(void*)*6);
if (v_exportMData_3616_ == 0)
{
lean_object* v_visitedNames_3617_; lean_object* v_visitedLevels_3618_; lean_object* v_visitedExprs_3619_; lean_object* v_visitedConstants_3620_; uint8_t v_exportUnsafe_3621_; uint8_t v_ignoreMissing_3622_; lean_object* v_recursorMap_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3644_; 
v_visitedNames_3617_ = lean_ctor_get(v_a_3614_, 0);
v_visitedLevels_3618_ = lean_ctor_get(v_a_3614_, 1);
v_visitedExprs_3619_ = lean_ctor_get(v_a_3614_, 2);
v_visitedConstants_3620_ = lean_ctor_get(v_a_3614_, 3);
v_exportUnsafe_3621_ = lean_ctor_get_uint8(v_a_3614_, sizeof(void*)*6 + 1);
v_ignoreMissing_3622_ = lean_ctor_get_uint8(v_a_3614_, sizeof(void*)*6 + 2);
v_recursorMap_3623_ = lean_ctor_get(v_a_3614_, 5);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3614_);
if (v_isSharedCheck_3644_ == 0)
{
lean_object* v_unused_3645_; 
v_unused_3645_ = lean_ctor_get(v_a_3614_, 4);
lean_dec(v_unused_3645_);
v___x_3625_ = v_a_3614_;
v_isShared_3626_ = v_isSharedCheck_3644_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_recursorMap_3623_);
lean_inc(v_visitedConstants_3620_);
lean_inc(v_visitedExprs_3619_);
lean_inc(v_visitedLevels_3618_);
lean_inc(v_visitedNames_3617_);
lean_dec(v_a_3614_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3644_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 4, v___x_3627_);
v___x_3629_ = v___x_3625_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_visitedNames_3617_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_visitedLevels_3618_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_visitedExprs_3619_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_visitedConstants_3620_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3643_, 5, v_recursorMap_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*6, v_exportMData_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*6 + 1, v_exportUnsafe_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3643_, sizeof(void*)*6 + 2, v_ignoreMissing_3622_);
v___x_3629_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3612_, v_a_3613_, v___x_3629_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_fst_3632_; lean_object* v_snd_3633_; lean_object* v___x_3634_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_fst_3632_ = lean_ctor_get(v_a_3631_, 0);
lean_inc(v_fst_3632_);
v_snd_3633_ = lean_ctor_get(v_a_3631_, 1);
lean_inc(v_snd_3633_);
lean_dec(v_a_3631_);
v___x_3634_ = l_LeanExport_dumpExprAux(v_fst_3632_, v_a_3613_, v_snd_3633_);
return v___x_3634_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3630_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3630_);
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
else
{
lean_object* v___x_3646_; 
v___x_3646_ = l_LeanExport_dumpExprAux(v_e_3612_, v_a_3613_, v_a_3614_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_bs_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_usize_dec_lt(v_i_3657_, v_sz_3656_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_bs_3658_);
lean_ctor_set(v___x_3663_, 1, v___y_3660_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
else
{
lean_object* v_v_3665_; lean_object* v_toConstantVal_3666_; lean_object* v_numParams_3667_; lean_object* v_numIndices_3668_; lean_object* v_all_3669_; lean_object* v_ctors_3670_; lean_object* v_numNested_3671_; uint8_t v_isRec_3672_; uint8_t v_isUnsafe_3673_; uint8_t v_isReflexive_3674_; lean_object* v_name_3675_; lean_object* v_levelParams_3676_; lean_object* v_type_3677_; lean_object* v___x_3678_; lean_object* v_bs_x27_3679_; lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___y_3688_; lean_object* v___x_3700_; 
v_v_3665_ = lean_array_uget_borrowed(v_bs_3658_, v_i_3657_);
v_toConstantVal_3666_ = lean_ctor_get(v_v_3665_, 0);
v_numParams_3667_ = lean_ctor_get(v_v_3665_, 1);
lean_inc(v_numParams_3667_);
v_numIndices_3668_ = lean_ctor_get(v_v_3665_, 2);
lean_inc(v_numIndices_3668_);
v_all_3669_ = lean_ctor_get(v_v_3665_, 3);
lean_inc(v_all_3669_);
v_ctors_3670_ = lean_ctor_get(v_v_3665_, 4);
lean_inc(v_ctors_3670_);
v_numNested_3671_ = lean_ctor_get(v_v_3665_, 5);
lean_inc(v_numNested_3671_);
v_isRec_3672_ = lean_ctor_get_uint8(v_v_3665_, sizeof(void*)*6);
v_isUnsafe_3673_ = lean_ctor_get_uint8(v_v_3665_, sizeof(void*)*6 + 1);
v_isReflexive_3674_ = lean_ctor_get_uint8(v_v_3665_, sizeof(void*)*6 + 2);
v_name_3675_ = lean_ctor_get(v_toConstantVal_3666_, 0);
lean_inc(v_name_3675_);
v_levelParams_3676_ = lean_ctor_get(v_toConstantVal_3666_, 1);
lean_inc(v_levelParams_3676_);
v_type_3677_ = lean_ctor_get(v_toConstantVal_3666_, 2);
lean_inc_ref(v_type_3677_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v_bs_x27_3679_ = lean_array_uset(v_bs_3658_, v_i_3657_, v___x_3678_);
v___x_3700_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3675_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v_fst_3702_; lean_object* v_snd_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3823_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v_fst_3702_ = lean_ctor_get(v_a_3701_, 0);
v_snd_3703_ = lean_ctor_get(v_a_3701_, 1);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3705_ = v_a_3701_;
v_isShared_3706_ = v_isSharedCheck_3823_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_snd_3703_);
lean_inc(v_fst_3702_);
lean_dec(v_a_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3823_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3676_, v___y_3659_, v_snd_3703_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3822_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3822_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3822_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_fst_3712_; lean_object* v_snd_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3821_; 
v_fst_3712_ = lean_ctor_get(v_a_3708_, 0);
v_snd_3713_ = lean_ctor_get(v_a_3708_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3715_ = v_a_3708_;
v_isShared_3716_ = v_isSharedCheck_3821_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_snd_3713_);
lean_inc(v_fst_3712_);
lean_dec(v_a_3708_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3821_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_LeanExport_dumpExpr(v_type_3677_, v___y_3659_, v_snd_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_fst_3719_; lean_object* v_snd_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3812_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v_fst_3719_ = lean_ctor_get(v_a_3718_, 0);
v_snd_3720_ = lean_ctor_get(v_a_3718_, 1);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_a_3718_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3722_ = v_a_3718_;
v_isShared_3723_ = v_isSharedCheck_3812_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_snd_3720_);
lean_inc(v_fst_3719_);
lean_dec(v_a_3718_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3812_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3669_, v___y_3659_, v_snd_3720_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3811_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3811_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3811_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_fst_3729_; lean_object* v_snd_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3810_; 
v_fst_3729_ = lean_ctor_get(v_a_3725_, 0);
v_snd_3730_ = lean_ctor_get(v_a_3725_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_a_3725_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3732_ = v_a_3725_;
v_isShared_3733_ = v_isSharedCheck_3810_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_snd_3730_);
lean_inc(v_fst_3729_);
lean_dec(v_a_3725_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3810_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; 
v___x_3734_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3670_, v___y_3659_, v_snd_3730_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3809_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3809_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3809_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v_fst_3739_; lean_object* v_snd_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3808_; 
v_fst_3739_ = lean_ctor_get(v_a_3735_, 0);
v_snd_3740_ = lean_ctor_get(v_a_3735_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_a_3735_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3742_ = v_a_3735_;
v_isShared_3743_ = v_isSharedCheck_3808_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_snd_3740_);
lean_inc(v_fst_3739_);
lean_dec(v_a_3735_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3808_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3745_ = l_Lean_JsonNumber_fromNat(v_fst_3702_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set_tag(v___x_3737_, 2);
lean_ctor_set(v___x_3737_, 0, v___x_3745_);
v___x_3747_ = v___x_3737_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 1, v___x_3747_);
lean_ctor_set(v___x_3742_, 0, v___x_3744_);
v___x_3749_ = v___x_3742_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 1, v_fst_3712_);
lean_ctor_set(v___x_3732_, 0, v___x_3750_);
v___x_3752_ = v___x_3732_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_fst_3712_);
v___x_3752_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3753_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3754_ = l_Lean_JsonNumber_fromNat(v_fst_3719_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 2);
lean_ctor_set(v___x_3727_, 0, v___x_3754_);
v___x_3756_ = v___x_3727_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 1, v___x_3756_);
lean_ctor_set(v___x_3722_, 0, v___x_3753_);
v___x_3758_ = v___x_3722_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3760_ = l_Lean_JsonNumber_fromNat(v_numParams_3667_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 2);
lean_ctor_set(v___x_3710_, 0, v___x_3760_);
v___x_3762_ = v___x_3710_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v___x_3762_);
lean_ctor_set(v___x_3715_, 0, v___x_3759_);
v___x_3764_ = v___x_3715_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_3766_ = l_Lean_JsonNumber_fromNat(v_numIndices_3668_);
v___x_3767_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v___x_3767_);
lean_ctor_set(v___x_3705_, 0, v___x_3765_);
v___x_3769_ = v___x_3705_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v_fst_3729_);
v___x_3772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v_fst_3739_);
v___x_3774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3));
v___x_3775_ = l_Lean_JsonNumber_fromNat(v_numNested_3671_);
v___x_3776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3774_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4));
v___x_3779_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3779_, 0, v_isRec_3672_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5));
v___x_3782_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3782_, 0, v_isReflexive_3674_);
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3785_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3785_, 0, v_isUnsafe_3673_);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = lean_box(0);
v___x_3788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3783_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3780_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3777_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3773_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3771_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3769_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3764_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3758_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3752_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3749_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = l_Lean_Json_mkObj(v___x_3798_);
lean_dec_ref_known(v___x_3798_, 2);
v_fst_3681_ = v___x_3799_;
v_snd_3682_ = v_snd_3740_;
goto v___jp_3680_;
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
lean_del_object(v___x_3732_);
lean_dec(v_fst_3729_);
lean_del_object(v___x_3727_);
lean_del_object(v___x_3722_);
lean_dec(v_fst_3719_);
lean_del_object(v___x_3715_);
lean_dec(v_fst_3712_);
lean_del_object(v___x_3710_);
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_dec(v_numNested_3671_);
lean_dec(v_numIndices_3668_);
lean_dec(v_numParams_3667_);
v___y_3688_ = v___x_3734_;
goto v___jp_3687_;
}
}
}
}
else
{
lean_del_object(v___x_3722_);
lean_dec(v_fst_3719_);
lean_del_object(v___x_3715_);
lean_dec(v_fst_3712_);
lean_del_object(v___x_3710_);
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_dec(v_numNested_3671_);
lean_dec(v_ctors_3670_);
lean_dec(v_numIndices_3668_);
lean_dec(v_numParams_3667_);
v___y_3688_ = v___x_3724_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3715_);
lean_dec(v_fst_3712_);
lean_del_object(v___x_3710_);
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_dec_ref(v_bs_x27_3679_);
lean_dec(v_numNested_3671_);
lean_dec(v_ctors_3670_);
lean_dec(v_all_3669_);
lean_dec(v_numIndices_3668_);
lean_dec(v_numParams_3667_);
v_a_3813_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3717_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3717_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_dec_ref(v_type_3677_);
lean_dec(v_numNested_3671_);
lean_dec(v_ctors_3670_);
lean_dec(v_all_3669_);
lean_dec(v_numIndices_3668_);
lean_dec(v_numParams_3667_);
v___y_3688_ = v___x_3707_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_bs_x27_3679_);
lean_dec_ref(v_type_3677_);
lean_dec(v_levelParams_3676_);
lean_dec(v_numNested_3671_);
lean_dec(v_ctors_3670_);
lean_dec(v_all_3669_);
lean_dec(v_numIndices_3668_);
lean_dec(v_numParams_3667_);
v_a_3824_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3700_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3700_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
v___jp_3680_:
{
size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_add(v_i_3657_, v___x_3683_);
v___x_3685_ = lean_array_uset(v_bs_x27_3679_, v_i_3657_, v_fst_3681_);
v_i_3657_ = v___x_3684_;
v_bs_3658_ = v___x_3685_;
v___y_3660_ = v_snd_3682_;
goto _start;
}
v___jp_3687_:
{
if (lean_obj_tag(v___y_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v_fst_3690_; lean_object* v_snd_3691_; 
v_a_3689_ = lean_ctor_get(v___y_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___y_3688_, 1);
v_fst_3690_ = lean_ctor_get(v_a_3689_, 0);
lean_inc(v_fst_3690_);
v_snd_3691_ = lean_ctor_get(v_a_3689_, 1);
lean_inc(v_snd_3691_);
lean_dec(v_a_3689_);
v_fst_3681_ = v_fst_3690_;
v_snd_3682_ = v_snd_3691_;
goto v___jp_3680_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_bs_x27_3679_);
v_a_3692_ = lean_ctor_get(v___y_3688_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___y_3688_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___y_3688_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___y_3688_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t v_sz_3835_, size_t v_i_3836_, lean_object* v_bs_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
uint8_t v___x_3841_; 
v___x_3841_ = lean_usize_dec_lt(v_i_3836_, v_sz_3835_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_bs_3837_);
lean_ctor_set(v___x_3842_, 1, v___y_3839_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
else
{
lean_object* v_v_3844_; lean_object* v_toConstantVal_3845_; lean_object* v_induct_3846_; lean_object* v_cidx_3847_; lean_object* v_numParams_3848_; lean_object* v_numFields_3849_; uint8_t v_isUnsafe_3850_; lean_object* v_name_3851_; lean_object* v_levelParams_3852_; lean_object* v_type_3853_; lean_object* v___x_3854_; lean_object* v_bs_x27_3855_; lean_object* v_fst_3857_; lean_object* v_snd_3858_; lean_object* v___x_3863_; 
v_v_3844_ = lean_array_uget_borrowed(v_bs_3837_, v_i_3836_);
v_toConstantVal_3845_ = lean_ctor_get(v_v_3844_, 0);
v_induct_3846_ = lean_ctor_get(v_v_3844_, 1);
lean_inc(v_induct_3846_);
v_cidx_3847_ = lean_ctor_get(v_v_3844_, 2);
lean_inc(v_cidx_3847_);
v_numParams_3848_ = lean_ctor_get(v_v_3844_, 3);
lean_inc(v_numParams_3848_);
v_numFields_3849_ = lean_ctor_get(v_v_3844_, 4);
lean_inc(v_numFields_3849_);
v_isUnsafe_3850_ = lean_ctor_get_uint8(v_v_3844_, sizeof(void*)*5);
v_name_3851_ = lean_ctor_get(v_toConstantVal_3845_, 0);
lean_inc(v_name_3851_);
v_levelParams_3852_ = lean_ctor_get(v_toConstantVal_3845_, 1);
lean_inc(v_levelParams_3852_);
v_type_3853_ = lean_ctor_get(v_toConstantVal_3845_, 2);
lean_inc_ref(v_type_3853_);
v___x_3854_ = lean_unsigned_to_nat(0u);
v_bs_x27_3855_ = lean_array_uset(v_bs_3837_, v_i_3836_, v___x_3854_);
v___x_3863_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3851_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3968_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v_fst_3865_ = lean_ctor_get(v_a_3864_, 0);
v_snd_3866_ = lean_ctor_get(v_a_3864_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_a_3864_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3868_ = v_a_3864_;
v_isShared_3869_ = v_isSharedCheck_3968_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_snd_3866_);
lean_inc(v_fst_3865_);
lean_dec(v_a_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3968_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; 
v___x_3870_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3852_, v___y_3838_, v_snd_3866_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_fst_3872_; lean_object* v_snd_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3956_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_fst_3872_ = lean_ctor_get(v_a_3871_, 0);
v_snd_3873_ = lean_ctor_get(v_a_3871_, 1);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3875_ = v_a_3871_;
v_isShared_3876_ = v_isSharedCheck_3956_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_snd_3873_);
lean_inc(v_fst_3872_);
lean_dec(v_a_3871_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3956_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_LeanExport_dumpExpr(v_type_3853_, v___y_3838_, v_snd_3873_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v_fst_3879_; lean_object* v_snd_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3947_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v_fst_3879_ = lean_ctor_get(v_a_3878_, 0);
v_snd_3880_ = lean_ctor_get(v_a_3878_, 1);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_a_3878_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3882_ = v_a_3878_;
v_isShared_3883_ = v_isSharedCheck_3947_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_snd_3880_);
lean_inc(v_fst_3879_);
lean_dec(v_a_3878_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3947_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; 
v___x_3884_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_3846_, v___y_3838_, v_snd_3880_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v_fst_3886_; lean_object* v_snd_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3938_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v_fst_3886_ = lean_ctor_get(v_a_3885_, 0);
v_snd_3887_ = lean_ctor_get(v_a_3885_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3885_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3889_ = v_a_3885_;
v_isShared_3890_ = v_isSharedCheck_3938_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_snd_3887_);
lean_inc(v_fst_3886_);
lean_dec(v_a_3885_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3938_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3892_ = l_Lean_JsonNumber_fromNat(v_fst_3865_);
v___x_3893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 1, v___x_3893_);
lean_ctor_set(v___x_3889_, 0, v___x_3891_);
v___x_3895_ = v___x_3889_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v_fst_3872_);
lean_ctor_set(v___x_3882_, 0, v___x_3896_);
v___x_3898_ = v___x_3882_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_fst_3872_);
v___x_3898_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3899_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3900_ = l_Lean_JsonNumber_fromNat(v_fst_3879_);
v___x_3901_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 1, v___x_3901_);
lean_ctor_set(v___x_3875_, 0, v___x_3899_);
v___x_3903_ = v___x_3875_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2));
v___x_3905_ = l_Lean_JsonNumber_fromNat(v_fst_3886_);
v___x_3906_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3906_);
lean_ctor_set(v___x_3868_, 0, v___x_3904_);
v___x_3908_ = v___x_3868_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3));
v___x_3910_ = l_Lean_JsonNumber_fromNat(v_cidx_3847_);
v___x_3911_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3909_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3914_ = l_Lean_JsonNumber_fromNat(v_numParams_3848_);
v___x_3915_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3913_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5));
v___x_3918_ = l_Lean_JsonNumber_fromNat(v_numFields_3849_);
v___x_3919_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3917_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3922_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3922_, 0, v_isUnsafe_3850_);
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3923_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3920_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3916_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3912_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3908_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3903_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3898_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3895_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = l_Lean_Json_mkObj(v___x_3932_);
lean_dec_ref_known(v___x_3932_, 2);
v_fst_3857_ = v___x_3933_;
v_snd_3858_ = v_snd_3887_;
goto v___jp_3856_;
}
}
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_del_object(v___x_3882_);
lean_dec(v_fst_3879_);
lean_del_object(v___x_3875_);
lean_dec(v_fst_3872_);
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec_ref(v_bs_x27_3855_);
lean_dec(v_numFields_3849_);
lean_dec(v_numParams_3848_);
lean_dec(v_cidx_3847_);
v_a_3939_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3884_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3884_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_del_object(v___x_3875_);
lean_dec(v_fst_3872_);
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec_ref(v_bs_x27_3855_);
lean_dec(v_numFields_3849_);
lean_dec(v_numParams_3848_);
lean_dec(v_cidx_3847_);
lean_dec(v_induct_3846_);
v_a_3948_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3877_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3877_);
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
lean_del_object(v___x_3868_);
lean_dec(v_fst_3865_);
lean_dec_ref(v_type_3853_);
lean_dec(v_numFields_3849_);
lean_dec(v_numParams_3848_);
lean_dec(v_cidx_3847_);
lean_dec(v_induct_3846_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3957_; lean_object* v_fst_3958_; lean_object* v_snd_3959_; 
v_a_3957_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3870_, 1);
v_fst_3958_ = lean_ctor_get(v_a_3957_, 0);
lean_inc(v_fst_3958_);
v_snd_3959_ = lean_ctor_get(v_a_3957_, 1);
lean_inc(v_snd_3959_);
lean_dec(v_a_3957_);
v_fst_3857_ = v_fst_3958_;
v_snd_3858_ = v_snd_3959_;
goto v___jp_3856_;
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec_ref(v_bs_x27_3855_);
v_a_3960_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3870_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3870_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec_ref(v_bs_x27_3855_);
lean_dec_ref(v_type_3853_);
lean_dec(v_levelParams_3852_);
lean_dec(v_numFields_3849_);
lean_dec(v_numParams_3848_);
lean_dec(v_cidx_3847_);
lean_dec(v_induct_3846_);
v_a_3969_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3863_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3863_);
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
v___jp_3856_:
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((size_t)1ULL);
v___x_3860_ = lean_usize_add(v_i_3836_, v___x_3859_);
v___x_3861_ = lean_array_uset(v_bs_x27_3855_, v_i_3836_, v_fst_3857_);
v_i_3836_ = v___x_3860_;
v_bs_3837_ = v___x_3861_;
v___y_3839_ = v_snd_3858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_ctor_3983_; lean_object* v_nfields_3984_; lean_object* v_rhs_3985_; lean_object* v___x_3986_; 
v_ctor_3983_ = lean_ctor_get(v_rule_3979_, 0);
lean_inc(v_ctor_3983_);
v_nfields_3984_ = lean_ctor_get(v_rule_3979_, 1);
lean_inc(v_nfields_3984_);
v_rhs_3985_ = lean_ctor_get(v_rule_3979_, 2);
lean_inc_ref(v_rhs_3985_);
lean_dec_ref(v_rule_3979_);
v___x_3986_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_3983_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v_fst_3988_; lean_object* v_snd_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4038_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v___x_3986_, 1);
v_fst_3988_ = lean_ctor_get(v_a_3987_, 0);
v_snd_3989_ = lean_ctor_get(v_a_3987_, 1);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_a_3987_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_3991_ = v_a_3987_;
v_isShared_3992_ = v_isSharedCheck_4038_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_snd_3989_);
lean_inc(v_fst_3988_);
lean_dec(v_a_3987_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4038_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_LeanExport_dumpExpr(v_rhs_3985_, v_a_3980_, v_snd_3989_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4029_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4029_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4029_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4028_; 
v_fst_3998_ = lean_ctor_get(v_a_3994_, 0);
v_snd_3999_ = lean_ctor_get(v_a_3994_, 1);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_a_3994_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4001_ = v_a_3994_;
v_isShared_4002_ = v_isSharedCheck_4028_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_snd_3999_);
lean_inc(v_fst_3998_);
lean_dec(v_a_3994_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4028_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_4003_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_4004_ = l_Lean_JsonNumber_fromNat(v_fst_3988_);
v___x_4005_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v___x_4005_);
lean_ctor_set(v___x_4001_, 0, v___x_4003_);
v___x_4007_ = v___x_4001_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4008_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_4009_ = l_Lean_JsonNumber_fromNat(v_nfields_3984_);
v___x_4010_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 1, v___x_4010_);
lean_ctor_set(v___x_3991_, 0, v___x_4008_);
v___x_4012_ = v___x_3991_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4008_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4013_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_4014_ = l_Lean_JsonNumber_fromNat(v_fst_3998_);
v___x_4015_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4013_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = lean_box(0);
v___x_4018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4016_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4012_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4007_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = l_Lean_Json_mkObj(v___x_4020_);
lean_dec_ref_known(v___x_4020_, 2);
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
lean_ctor_set(v___x_4022_, 1, v_snd_3999_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4022_);
v___x_4024_ = v___x_3996_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_del_object(v___x_3991_);
lean_dec(v_fst_3988_);
lean_dec(v_nfields_3984_);
v_a_4030_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_3993_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_3993_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec_ref(v_rhs_3985_);
lean_dec(v_nfields_3984_);
v_a_4039_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_3986_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_3986_);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4047_, lean_object* v_x_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_){
_start:
{
if (lean_obj_tag(v_x_4047_) == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = l_List_reverse___redArg(v_x_4048_);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___y_4050_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
else
{
lean_object* v_head_4055_; lean_object* v_tail_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4076_; 
v_head_4055_ = lean_ctor_get(v_x_4047_, 0);
v_tail_4056_ = lean_ctor_get(v_x_4047_, 1);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_x_4047_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4058_ = v_x_4047_;
v_isShared_4059_ = v_isSharedCheck_4076_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_tail_4056_);
lean_inc(v_head_4055_);
lean_dec(v_x_4047_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4076_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; 
v___x_4060_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4055_, v___y_4049_, v___y_4050_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4065_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v_fst_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_fst_4062_);
v_snd_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4063_);
lean_dec(v_a_4061_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v_x_4048_);
lean_ctor_set(v___x_4058_, 0, v_fst_4062_);
v___x_4065_ = v___x_4058_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_fst_4062_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_x_4048_);
v___x_4065_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
v_x_4047_ = v_tail_4056_;
v_x_4048_ = v___x_4065_;
v___y_4050_ = v_snd_4063_;
goto _start;
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_del_object(v___x_4058_);
lean_dec(v_tail_4056_);
lean_dec(v_x_4048_);
v_a_4068_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4060_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4060_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_4081_, size_t v_i_4082_, lean_object* v_bs_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v___x_4087_; 
v___x_4087_ = lean_usize_dec_lt(v_i_4082_, v_sz_4081_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v_bs_4083_);
lean_ctor_set(v___x_4088_, 1, v___y_4085_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
else
{
lean_object* v_v_4090_; lean_object* v_toConstantVal_4091_; lean_object* v_all_4092_; lean_object* v_numParams_4093_; lean_object* v_numIndices_4094_; lean_object* v_numMotives_4095_; lean_object* v_numMinors_4096_; lean_object* v_rules_4097_; uint8_t v_k_4098_; uint8_t v_isUnsafe_4099_; lean_object* v_name_4100_; lean_object* v_levelParams_4101_; lean_object* v_type_4102_; lean_object* v___x_4103_; lean_object* v_bs_x27_4104_; lean_object* v_fst_4106_; lean_object* v_snd_4107_; lean_object* v___y_4113_; lean_object* v___x_4125_; 
v_v_4090_ = lean_array_uget_borrowed(v_bs_4083_, v_i_4082_);
v_toConstantVal_4091_ = lean_ctor_get(v_v_4090_, 0);
v_all_4092_ = lean_ctor_get(v_v_4090_, 1);
lean_inc(v_all_4092_);
v_numParams_4093_ = lean_ctor_get(v_v_4090_, 2);
lean_inc(v_numParams_4093_);
v_numIndices_4094_ = lean_ctor_get(v_v_4090_, 3);
lean_inc(v_numIndices_4094_);
v_numMotives_4095_ = lean_ctor_get(v_v_4090_, 4);
lean_inc(v_numMotives_4095_);
v_numMinors_4096_ = lean_ctor_get(v_v_4090_, 5);
lean_inc(v_numMinors_4096_);
v_rules_4097_ = lean_ctor_get(v_v_4090_, 6);
lean_inc(v_rules_4097_);
v_k_4098_ = lean_ctor_get_uint8(v_v_4090_, sizeof(void*)*7);
v_isUnsafe_4099_ = lean_ctor_get_uint8(v_v_4090_, sizeof(void*)*7 + 1);
v_name_4100_ = lean_ctor_get(v_toConstantVal_4091_, 0);
lean_inc(v_name_4100_);
v_levelParams_4101_ = lean_ctor_get(v_toConstantVal_4091_, 1);
lean_inc(v_levelParams_4101_);
v_type_4102_ = lean_ctor_get(v_toConstantVal_4091_, 2);
lean_inc_ref(v_type_4102_);
v___x_4103_ = lean_unsigned_to_nat(0u);
v_bs_x27_4104_ = lean_array_uset(v_bs_4083_, v_i_4082_, v___x_4103_);
v___x_4125_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4100_, v___y_4084_, v___y_4085_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v_fst_4127_; lean_object* v_snd_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4252_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v_fst_4127_ = lean_ctor_get(v_a_4126_, 0);
v_snd_4128_ = lean_ctor_get(v_a_4126_, 1);
v_isSharedCheck_4252_ = !lean_is_exclusive(v_a_4126_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4130_ = v_a_4126_;
v_isShared_4131_ = v_isSharedCheck_4252_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_snd_4128_);
lean_inc(v_fst_4127_);
lean_dec(v_a_4126_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4252_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; 
v___x_4132_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4101_, v___y_4084_, v_snd_4128_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4251_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4135_ = v___x_4132_;
v_isShared_4136_ = v_isSharedCheck_4251_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4132_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4251_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v_fst_4137_; lean_object* v_snd_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4250_; 
v_fst_4137_ = lean_ctor_get(v_a_4133_, 0);
v_snd_4138_ = lean_ctor_get(v_a_4133_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_a_4133_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4140_ = v_a_4133_;
v_isShared_4141_ = v_isSharedCheck_4250_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_snd_4138_);
lean_inc(v_fst_4137_);
lean_dec(v_a_4133_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4250_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_LeanExport_dumpExpr(v_type_4102_, v___y_4084_, v_snd_4138_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v_fst_4144_; lean_object* v_snd_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4241_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v_fst_4144_ = lean_ctor_get(v_a_4143_, 0);
v_snd_4145_ = lean_ctor_get(v_a_4143_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_a_4143_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4147_ = v_a_4143_;
v_isShared_4148_ = v_isSharedCheck_4241_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_snd_4145_);
lean_inc(v_fst_4144_);
lean_dec(v_a_4143_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4241_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; 
v___x_4149_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4092_, v___y_4084_, v_snd_4145_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4240_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4240_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4240_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_fst_4154_; lean_object* v_snd_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4239_; 
v_fst_4154_ = lean_ctor_get(v_a_4150_, 0);
v_snd_4155_ = lean_ctor_get(v_a_4150_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_a_4150_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4157_ = v_a_4150_;
v_isShared_4158_ = v_isSharedCheck_4239_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_snd_4155_);
lean_inc(v_fst_4154_);
lean_dec(v_a_4150_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4239_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = lean_box(0);
v___x_4160_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4097_, v___x_4159_, v___y_4084_, v_snd_4155_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v_fst_4162_; lean_object* v_snd_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4230_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v_fst_4162_ = lean_ctor_get(v_a_4161_, 0);
v_snd_4163_ = lean_ctor_get(v_a_4161_, 1);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_a_4161_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4165_ = v_a_4161_;
v_isShared_4166_ = v_isSharedCheck_4230_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_snd_4163_);
lean_inc(v_fst_4162_);
lean_dec(v_a_4161_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4230_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4168_ = l_Lean_JsonNumber_fromNat(v_fst_4127_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set_tag(v___x_4152_, 2);
lean_ctor_set(v___x_4152_, 0, v___x_4168_);
v___x_4170_ = v___x_4152_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4172_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___x_4170_);
lean_ctor_set(v___x_4165_, 0, v___x_4167_);
v___x_4172_ = v___x_4165_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v_fst_4137_);
lean_ctor_set(v___x_4157_, 0, v___x_4173_);
v___x_4175_ = v___x_4157_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_fst_4137_);
v___x_4175_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4176_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4177_ = l_Lean_JsonNumber_fromNat(v_fst_4144_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set_tag(v___x_4135_, 2);
lean_ctor_set(v___x_4135_, 0, v___x_4177_);
v___x_4179_ = v___x_4135_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4181_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 1, v___x_4179_);
lean_ctor_set(v___x_4147_, 0, v___x_4176_);
v___x_4181_ = v___x_4147_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v_fst_4154_);
lean_ctor_set(v___x_4140_, 0, v___x_4182_);
v___x_4184_ = v___x_4140_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4182_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_fst_4154_);
v___x_4184_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_4186_ = l_Lean_JsonNumber_fromNat(v_numParams_4093_);
v___x_4187_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 1, v___x_4187_);
lean_ctor_set(v___x_4130_, 0, v___x_4185_);
v___x_4189_ = v___x_4130_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_4191_ = l_Lean_JsonNumber_fromNat(v_numIndices_4094_);
v___x_4192_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4190_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4195_ = l_Lean_JsonNumber_fromNat(v_numMotives_4095_);
v___x_4196_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4194_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_4199_ = l_Lean_JsonNumber_fromNat(v_numMinors_4096_);
v___x_4200_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4198_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4203_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4162_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_4206_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4206_, 0, v_k_4098_);
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4209_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4209_, 0, v_isUnsafe_4099_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4208_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4159_);
v___x_4212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4207_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___x_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4204_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4201_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4197_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4193_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4189_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4184_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4181_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4175_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
v___x_4221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4172_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
v___x_4222_ = l_Lean_Json_mkObj(v___x_4221_);
lean_dec_ref_known(v___x_4221_, 2);
v_fst_4106_ = v___x_4222_;
v_snd_4107_ = v_snd_4163_;
goto v___jp_4105_;
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
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_del_object(v___x_4157_);
lean_dec(v_fst_4154_);
lean_del_object(v___x_4152_);
lean_del_object(v___x_4147_);
lean_dec(v_fst_4144_);
lean_del_object(v___x_4140_);
lean_dec(v_fst_4137_);
lean_del_object(v___x_4135_);
lean_del_object(v___x_4130_);
lean_dec(v_fst_4127_);
lean_dec_ref(v_bs_x27_4104_);
lean_dec(v_numMinors_4096_);
lean_dec(v_numMotives_4095_);
lean_dec(v_numIndices_4094_);
lean_dec(v_numParams_4093_);
v_a_4231_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4160_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4160_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4147_);
lean_dec(v_fst_4144_);
lean_del_object(v___x_4140_);
lean_dec(v_fst_4137_);
lean_del_object(v___x_4135_);
lean_del_object(v___x_4130_);
lean_dec(v_fst_4127_);
lean_dec(v_rules_4097_);
lean_dec(v_numMinors_4096_);
lean_dec(v_numMotives_4095_);
lean_dec(v_numIndices_4094_);
lean_dec(v_numParams_4093_);
v___y_4113_ = v___x_4149_;
goto v___jp_4112_;
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_del_object(v___x_4140_);
lean_dec(v_fst_4137_);
lean_del_object(v___x_4135_);
lean_del_object(v___x_4130_);
lean_dec(v_fst_4127_);
lean_dec_ref(v_bs_x27_4104_);
lean_dec(v_rules_4097_);
lean_dec(v_numMinors_4096_);
lean_dec(v_numMotives_4095_);
lean_dec(v_numIndices_4094_);
lean_dec(v_numParams_4093_);
lean_dec(v_all_4092_);
v_a_4242_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4142_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4142_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4130_);
lean_dec(v_fst_4127_);
lean_dec_ref(v_type_4102_);
lean_dec(v_rules_4097_);
lean_dec(v_numMinors_4096_);
lean_dec(v_numMotives_4095_);
lean_dec(v_numIndices_4094_);
lean_dec(v_numParams_4093_);
lean_dec(v_all_4092_);
v___y_4113_ = v___x_4132_;
goto v___jp_4112_;
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v_bs_x27_4104_);
lean_dec_ref(v_type_4102_);
lean_dec(v_levelParams_4101_);
lean_dec(v_rules_4097_);
lean_dec(v_numMinors_4096_);
lean_dec(v_numMotives_4095_);
lean_dec(v_numIndices_4094_);
lean_dec(v_numParams_4093_);
lean_dec(v_all_4092_);
v_a_4253_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4125_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4125_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
v___jp_4105_:
{
size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4108_ = ((size_t)1ULL);
v___x_4109_ = lean_usize_add(v_i_4082_, v___x_4108_);
v___x_4110_ = lean_array_uset(v_bs_x27_4104_, v_i_4082_, v_fst_4106_);
v_i_4082_ = v___x_4109_;
v_bs_4083_ = v___x_4110_;
v___y_4085_ = v_snd_4107_;
goto _start;
}
v___jp_4112_:
{
if (lean_obj_tag(v___y_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v_fst_4115_; lean_object* v_snd_4116_; 
v_a_4114_ = lean_ctor_get(v___y_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___y_4113_, 1);
v_fst_4115_ = lean_ctor_get(v_a_4114_, 0);
lean_inc(v_fst_4115_);
v_snd_4116_ = lean_ctor_get(v_a_4114_, 1);
lean_inc(v_snd_4116_);
lean_dec(v_a_4114_);
v_fst_4106_ = v_fst_4115_;
v_snd_4107_ = v_snd_4116_;
goto v___jp_4105_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_bs_x27_4104_);
v_a_4117_ = lean_ctor_get(v___y_4113_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___y_4113_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___y_4113_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___y_4113_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4309_, lean_object* v_as_x27_4310_, lean_object* v_b_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
if (lean_obj_tag(v_as_x27_4310_) == 0)
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4315_, 0, v_b_4311_);
lean_ctor_set(v___x_4315_, 1, v___y_4313_);
v___x_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
return v___x_4316_;
}
else
{
lean_object* v_head_4317_; lean_object* v_tail_4318_; lean_object* v___x_4319_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___x_4350_; 
lean_dec_ref(v_b_4311_);
v_head_4317_ = lean_ctor_get(v_as_x27_4310_, 0);
v_tail_4318_ = lean_ctor_get(v_as_x27_4310_, 1);
v___x_4319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4317_);
lean_inc_ref(v___y_4312_);
v___x_4350_ = l_Lean_Environment_find_x3f(v___y_4312_, v_head_4317_, v___x_4309_);
if (lean_obj_tag(v___x_4350_) == 1)
{
lean_object* v_val_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4474_; 
v_val_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4474_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_val_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4474_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
if (lean_obj_tag(v_val_4351_) == 4)
{
lean_object* v_val_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4473_; 
v_val_4355_ = lean_ctor_get(v_val_4351_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_val_4351_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4357_ = v_val_4351_;
v_isShared_4358_ = v_isSharedCheck_4473_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_val_4355_);
lean_dec(v_val_4351_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4473_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v_toConstantVal_4359_; lean_object* v_visitedNames_4360_; lean_object* v_visitedLevels_4361_; lean_object* v_visitedExprs_4362_; lean_object* v_visitedConstants_4363_; lean_object* v_noMDataExprs_4364_; uint8_t v_exportMData_4365_; uint8_t v_exportUnsafe_4366_; uint8_t v_ignoreMissing_4367_; lean_object* v_recursorMap_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4472_; 
v_toConstantVal_4359_ = lean_ctor_get(v_val_4355_, 0);
lean_inc_ref(v_toConstantVal_4359_);
v_visitedNames_4360_ = lean_ctor_get(v___y_4313_, 0);
v_visitedLevels_4361_ = lean_ctor_get(v___y_4313_, 1);
v_visitedExprs_4362_ = lean_ctor_get(v___y_4313_, 2);
v_visitedConstants_4363_ = lean_ctor_get(v___y_4313_, 3);
v_noMDataExprs_4364_ = lean_ctor_get(v___y_4313_, 4);
v_exportMData_4365_ = lean_ctor_get_uint8(v___y_4313_, sizeof(void*)*6);
v_exportUnsafe_4366_ = lean_ctor_get_uint8(v___y_4313_, sizeof(void*)*6 + 1);
v_ignoreMissing_4367_ = lean_ctor_get_uint8(v___y_4313_, sizeof(void*)*6 + 2);
v_recursorMap_4368_ = lean_ctor_get(v___y_4313_, 5);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___y_4313_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4370_ = v___y_4313_;
v_isShared_4371_ = v_isSharedCheck_4472_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_recursorMap_4368_);
lean_inc(v_noMDataExprs_4364_);
lean_inc(v_visitedConstants_4363_);
lean_inc(v_visitedExprs_4362_);
lean_inc(v_visitedLevels_4361_);
lean_inc(v_visitedNames_4360_);
lean_dec(v___y_4313_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4472_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
uint8_t v_kind_4372_; lean_object* v_name_4373_; lean_object* v_levelParams_4374_; lean_object* v_type_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v_kind_4372_ = lean_ctor_get_uint8(v_val_4355_, sizeof(void*)*1);
lean_dec_ref(v_val_4355_);
v_name_4373_ = lean_ctor_get(v_toConstantVal_4359_, 0);
lean_inc(v_name_4373_);
v_levelParams_4374_ = lean_ctor_get(v_toConstantVal_4359_, 1);
lean_inc(v_levelParams_4374_);
v_type_4375_ = lean_ctor_get(v_toConstantVal_4359_, 2);
lean_inc_ref(v_type_4375_);
lean_dec_ref(v_toConstantVal_4359_);
lean_inc(v_head_4317_);
v___x_4376_ = l_Lean_NameHashSet_insert(v_visitedConstants_4363_, v_head_4317_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 3, v___x_4376_);
v___x_4378_ = v___x_4370_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_visitedNames_4360_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_visitedLevels_4361_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_visitedExprs_4362_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_noMDataExprs_4364_);
lean_ctor_set(v_reuseFailAlloc_4471_, 5, v_recursorMap_4368_);
lean_ctor_set_uint8(v_reuseFailAlloc_4471_, sizeof(void*)*6, v_exportMData_4365_);
lean_ctor_set_uint8(v_reuseFailAlloc_4471_, sizeof(void*)*6 + 1, v_exportUnsafe_4366_);
lean_ctor_set_uint8(v_reuseFailAlloc_4471_, sizeof(void*)*6 + 2, v_ignoreMissing_4367_);
v___x_4378_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; 
v___x_4379_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4373_, v___y_4312_, v___x_4378_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v_fst_4381_; lean_object* v_snd_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4462_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v_fst_4381_ = lean_ctor_get(v_a_4380_, 0);
v_snd_4382_ = lean_ctor_get(v_a_4380_, 1);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_a_4380_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4384_ = v_a_4380_;
v_isShared_4385_ = v_isSharedCheck_4462_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_snd_4382_);
lean_inc(v_fst_4381_);
lean_dec(v_a_4380_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4462_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; 
v___x_4386_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4374_, v___y_4312_, v_snd_4382_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v_fst_4388_; lean_object* v_snd_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4453_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
v_fst_4388_ = lean_ctor_get(v_a_4387_, 0);
v_snd_4389_ = lean_ctor_get(v_a_4387_, 1);
v_isSharedCheck_4453_ = !lean_is_exclusive(v_a_4387_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4391_ = v_a_4387_;
v_isShared_4392_ = v_isSharedCheck_4453_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_snd_4389_);
lean_inc(v_fst_4388_);
lean_dec(v_a_4387_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4453_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_LeanExport_dumpExpr(v_type_4375_, v___y_4312_, v_snd_4389_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v_fst_4395_; lean_object* v_snd_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4444_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v___x_4393_, 1);
v_fst_4395_ = lean_ctor_get(v_a_4394_, 0);
v_snd_4396_ = lean_ctor_get(v_a_4394_, 1);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_a_4394_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4398_ = v_a_4394_;
v_isShared_4399_ = v_isSharedCheck_4444_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_snd_4396_);
lean_inc(v_fst_4395_);
lean_dec(v_a_4394_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4444_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4400_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4402_ = l_Lean_JsonNumber_fromNat(v_fst_4381_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set_tag(v___x_4357_, 2);
lean_ctor_set(v___x_4357_, 0, v___x_4402_);
v___x_4404_ = v___x_4357_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4406_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 1, v___x_4404_);
lean_ctor_set(v___x_4398_, 0, v___x_4401_);
v___x_4406_ = v___x_4398_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 1, v_fst_4388_);
lean_ctor_set(v___x_4391_, 0, v___x_4407_);
v___x_4409_ = v___x_4391_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4407_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_fst_4388_);
v___x_4409_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4410_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4411_ = l_Lean_JsonNumber_fromNat(v_fst_4395_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set_tag(v___x_4353_, 2);
lean_ctor_set(v___x_4353_, 0, v___x_4411_);
v___x_4413_ = v___x_4353_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4415_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 1, v___x_4413_);
lean_ctor_set(v___x_4384_, 0, v___x_4410_);
v___x_4415_ = v___x_4384_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4416_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4417_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4372_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = lean_box(0);
v___x_4420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4415_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4409_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4406_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = l_Lean_Json_mkObj(v___x_4423_);
lean_dec_ref_known(v___x_4423_, 2);
v___x_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4400_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
lean_ctor_set(v___x_4426_, 1, v___x_4419_);
v___x_4427_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4426_, v_snd_4396_);
lean_dec_ref_known(v___x_4426_, 2);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v_snd_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v_snd_4429_ = lean_ctor_get(v_a_4428_, 1);
lean_inc(v_snd_4429_);
lean_dec(v_a_4428_);
v_as_x27_4310_ = v_tail_4318_;
v_b_4311_ = v___x_4319_;
v___y_4313_ = v_snd_4429_;
goto _start;
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
v_a_4431_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4427_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4427_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
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
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_del_object(v___x_4391_);
lean_dec(v_fst_4388_);
lean_del_object(v___x_4384_);
lean_dec(v_fst_4381_);
lean_del_object(v___x_4357_);
lean_del_object(v___x_4353_);
v_a_4445_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4393_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4393_);
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
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_del_object(v___x_4384_);
lean_dec(v_fst_4381_);
lean_dec_ref(v_type_4375_);
lean_del_object(v___x_4357_);
lean_del_object(v___x_4353_);
v_a_4454_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4386_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4386_);
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
lean_dec_ref(v_type_4375_);
lean_dec(v_levelParams_4374_);
lean_del_object(v___x_4357_);
lean_del_object(v___x_4353_);
v_a_4463_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4379_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4379_);
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
}
}
else
{
lean_del_object(v___x_4353_);
lean_dec(v_val_4351_);
v___y_4321_ = v___y_4312_;
v___y_4322_ = v___y_4313_;
goto v___jp_4320_;
}
}
}
else
{
lean_dec(v___x_4350_);
v___y_4321_ = v___y_4312_;
v___y_4322_ = v___y_4313_;
goto v___jp_4320_;
}
v___jp_4320_:
{
uint8_t v_ignoreMissing_4323_; 
v_ignoreMissing_4323_ = lean_ctor_get_uint8(v___y_4322_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4323_ == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4324_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4325_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4326_ = lean_unsigned_to_nat(313u);
v___x_4327_ = lean_unsigned_to_nat(52u);
v___x_4328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4329_ = 1;
lean_inc(v_head_4317_);
v___x_4330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4317_, v___x_4329_);
v___x_4331_ = lean_string_append(v___x_4328_, v___x_4330_);
lean_dec_ref(v___x_4330_);
v___x_4332_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4333_ = lean_string_append(v___x_4331_, v___x_4332_);
v___x_4334_ = l_mkPanicMessageWithDecl(v___x_4324_, v___x_4325_, v___x_4326_, v___x_4327_, v___x_4333_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4334_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v_snd_4337_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v_snd_4337_ = lean_ctor_get(v_a_4336_, 1);
lean_inc(v_snd_4337_);
lean_dec(v_a_4336_);
v_as_x27_4310_ = v_tail_4318_;
v_b_4311_ = v___x_4319_;
v___y_4313_ = v_snd_4337_;
goto _start;
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
v_a_4339_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4335_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4335_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4347_);
lean_ctor_set(v___x_4348_, 1, v___y_4322_);
v___x_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4348_);
return v___x_4349_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4477_ = l_Lean_NameSet_empty;
v___x_4478_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
lean_ctor_set(v___x_4479_, 1, v___x_4477_);
return v___x_4479_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4480_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4481_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
lean_ctor_set(v___x_4482_, 1, v___x_4480_);
return v___x_4482_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4486_ = lean_unsigned_to_nat(11u);
v___x_4487_ = lean_unsigned_to_nat(341u);
v___x_4488_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4489_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4490_ = l_mkPanicMessageWithDecl(v___x_4489_, v___x_4488_, v___x_4487_, v___x_4486_, v___x_4485_);
return v___x_4490_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4492_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4493_ = lean_unsigned_to_nat(6u);
v___x_4494_ = lean_unsigned_to_nat(329u);
v___x_4495_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4496_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4497_ = l_mkPanicMessageWithDecl(v___x_4496_, v___x_4495_, v___x_4494_, v___x_4493_, v___x_4492_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4498_, lean_object* v_val_4499_, lean_object* v_as_x27_4500_, lean_object* v_b_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
if (lean_obj_tag(v_as_x27_4500_) == 0)
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v_b_4501_);
lean_ctor_set(v___x_4505_, 1, v___y_4503_);
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
else
{
lean_object* v_head_4507_; lean_object* v_tail_4508_; lean_object* v___y_4510_; lean_object* v_snd_4541_; lean_object* v_fst_4542_; lean_object* v_fst_4543_; lean_object* v_snd_4544_; lean_object* v___y_4546_; uint8_t v___y_4547_; lean_object* v___y_4628_; lean_object* v___x_4635_; 
v_head_4507_ = lean_ctor_get(v_as_x27_4500_, 0);
v_tail_4508_ = lean_ctor_get(v_as_x27_4500_, 1);
v_snd_4541_ = lean_ctor_get(v_b_4501_, 1);
lean_inc(v_snd_4541_);
v_fst_4542_ = lean_ctor_get(v_b_4501_, 0);
lean_inc(v_fst_4542_);
lean_dec_ref(v_b_4501_);
v_fst_4543_ = lean_ctor_get(v_snd_4541_, 0);
lean_inc(v_fst_4543_);
v_snd_4544_ = lean_ctor_get(v_snd_4541_, 1);
lean_inc(v_snd_4544_);
lean_dec(v_snd_4541_);
lean_inc(v_head_4507_);
lean_inc_ref(v___y_4502_);
v___x_4635_ = l_Lean_Environment_find_x3f(v___y_4502_, v_head_4507_, v___x_4498_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_4637_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4636_);
v___y_4628_ = v___x_4637_;
goto v___jp_4627_;
}
else
{
lean_object* v_val_4638_; 
v_val_4638_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_val_4638_);
lean_dec_ref_known(v___x_4635_, 1);
v___y_4628_ = v_val_4638_;
goto v___jp_4627_;
}
v___jp_4509_:
{
if (lean_obj_tag(v___y_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4532_; 
v_a_4511_ = lean_ctor_get(v___y_4510_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___y_4510_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4513_ = v___y_4510_;
v_isShared_4514_ = v_isSharedCheck_4532_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___y_4510_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4532_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v_fst_4515_; 
v_fst_4515_ = lean_ctor_get(v_a_4511_, 0);
lean_inc(v_fst_4515_);
if (lean_obj_tag(v_fst_4515_) == 0)
{
lean_object* v_snd_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4527_; 
v_snd_4516_ = lean_ctor_get(v_a_4511_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_a_4511_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v_a_4511_, 0);
lean_dec(v_unused_4528_);
v___x_4518_ = v_a_4511_;
v_isShared_4519_ = v_isSharedCheck_4527_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_snd_4516_);
lean_dec(v_a_4511_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4527_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v_a_4520_; lean_object* v___x_4522_; 
v_a_4520_ = lean_ctor_get(v_fst_4515_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v_fst_4515_, 1);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v_a_4520_);
v___x_4522_ = v___x_4518_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_snd_4516_);
v___x_4522_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4524_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4522_);
v___x_4524_ = v___x_4513_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_snd_4529_; lean_object* v_a_4530_; 
lean_del_object(v___x_4513_);
v_snd_4529_ = lean_ctor_get(v_a_4511_, 1);
lean_inc(v_snd_4529_);
lean_dec(v_a_4511_);
v_a_4530_ = lean_ctor_get(v_fst_4515_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v_fst_4515_, 1);
v_as_x27_4500_ = v_tail_4508_;
v_b_4501_ = v_a_4530_;
v___y_4503_ = v_snd_4529_;
goto _start;
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
v_a_4533_ = lean_ctor_get(v___y_4510_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___y_4510_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___y_4510_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___y_4510_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_4545_:
{
lean_object* v_toConstantVal_4548_; lean_object* v_ctors_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v_toConstantVal_4548_ = lean_ctor_get(v___y_4546_, 0);
lean_inc_ref(v_toConstantVal_4548_);
v_ctors_4549_ = lean_ctor_get(v___y_4546_, 4);
lean_inc(v_ctors_4549_);
v___x_4550_ = lean_array_push(v_fst_4542_, v___y_4546_);
v___x_4551_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4547_, v___x_4498_, v_ctors_4549_, v_fst_4543_, v___y_4502_, v___y_4503_);
lean_dec(v_ctors_4549_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_snd_4553_; lean_object* v_fst_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4618_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
v_snd_4553_ = lean_ctor_get(v_a_4552_, 1);
v_fst_4554_ = lean_ctor_get(v_a_4552_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_a_4552_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4556_ = v_a_4552_;
v_isShared_4557_ = v_isSharedCheck_4618_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_snd_4553_);
lean_inc(v_fst_4554_);
lean_dec(v_a_4552_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4618_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v_visitedNames_4558_; lean_object* v_visitedLevels_4559_; lean_object* v_visitedExprs_4560_; lean_object* v_visitedConstants_4561_; lean_object* v_noMDataExprs_4562_; uint8_t v_exportMData_4563_; uint8_t v_exportUnsafe_4564_; uint8_t v_ignoreMissing_4565_; lean_object* v_recursorMap_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4617_; 
v_visitedNames_4558_ = lean_ctor_get(v_snd_4553_, 0);
v_visitedLevels_4559_ = lean_ctor_get(v_snd_4553_, 1);
v_visitedExprs_4560_ = lean_ctor_get(v_snd_4553_, 2);
v_visitedConstants_4561_ = lean_ctor_get(v_snd_4553_, 3);
v_noMDataExprs_4562_ = lean_ctor_get(v_snd_4553_, 4);
v_exportMData_4563_ = lean_ctor_get_uint8(v_snd_4553_, sizeof(void*)*6);
v_exportUnsafe_4564_ = lean_ctor_get_uint8(v_snd_4553_, sizeof(void*)*6 + 1);
v_ignoreMissing_4565_ = lean_ctor_get_uint8(v_snd_4553_, sizeof(void*)*6 + 2);
v_recursorMap_4566_ = lean_ctor_get(v_snd_4553_, 5);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_snd_4553_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4568_ = v_snd_4553_;
v_isShared_4569_ = v_isSharedCheck_4617_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_recursorMap_4566_);
lean_inc(v_noMDataExprs_4562_);
lean_inc(v_visitedConstants_4561_);
lean_inc(v_visitedExprs_4560_);
lean_inc(v_visitedLevels_4559_);
lean_inc(v_visitedNames_4558_);
lean_dec(v_snd_4553_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4617_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v_type_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
v_type_4570_ = lean_ctor_get(v_toConstantVal_4548_, 2);
lean_inc_ref(v_type_4570_);
lean_dec_ref(v_toConstantVal_4548_);
lean_inc(v_head_4507_);
v___x_4571_ = l_Lean_NameHashSet_insert(v_visitedConstants_4561_, v_head_4507_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 3, v___x_4571_);
v___x_4573_ = v___x_4568_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_visitedNames_4558_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_visitedLevels_4559_);
lean_ctor_set(v_reuseFailAlloc_4616_, 2, v_visitedExprs_4560_);
lean_ctor_set(v_reuseFailAlloc_4616_, 3, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4616_, 4, v_noMDataExprs_4562_);
lean_ctor_set(v_reuseFailAlloc_4616_, 5, v_recursorMap_4566_);
lean_ctor_set_uint8(v_reuseFailAlloc_4616_, sizeof(void*)*6, v_exportMData_4563_);
lean_ctor_set_uint8(v_reuseFailAlloc_4616_, sizeof(void*)*6 + 1, v_exportUnsafe_4564_);
lean_ctor_set_uint8(v_reuseFailAlloc_4616_, sizeof(void*)*6 + 2, v_ignoreMissing_4565_);
v___x_4573_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
lean_object* v___x_4574_; 
v___x_4574_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4570_, v___y_4502_, v___x_4573_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_snd_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4606_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
v_snd_4576_ = lean_ctor_get(v_a_4575_, 1);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_a_4575_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; 
v_unused_4607_ = lean_ctor_get(v_a_4575_, 0);
lean_dec(v_unused_4607_);
v___x_4578_ = v_a_4575_;
v_isShared_4579_ = v_isSharedCheck_4606_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_snd_4576_);
lean_dec(v_a_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4606_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v_toConstantVal_4580_; lean_object* v_recursorMap_4581_; lean_object* v_name_4582_; lean_object* v___x_4583_; 
v_toConstantVal_4580_ = lean_ctor_get(v_val_4499_, 0);
v_recursorMap_4581_ = lean_ctor_get(v_snd_4576_, 5);
v_name_4582_ = lean_ctor_get(v_toConstantVal_4580_, 0);
v___x_4583_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4581_, v_name_4582_);
if (lean_obj_tag(v___x_4583_) == 1)
{
lean_object* v_val_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4588_; 
v_val_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_val_4584_);
lean_dec_ref_known(v___x_4583_, 1);
v___x_4585_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4586_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4585_, v_snd_4544_, v_val_4584_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 1, v___x_4586_);
lean_ctor_set(v___x_4578_, 0, v_fst_4554_);
v___x_4588_ = v___x_4578_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_fst_4554_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4590_; 
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v___x_4588_);
lean_ctor_set(v___x_4556_, 0, v___x_4550_);
v___x_4590_ = v___x_4556_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v___x_4588_);
v___x_4590_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
v_as_x27_4500_ = v_tail_4508_;
v_b_4501_ = v___x_4590_;
v___y_4503_ = v_snd_4576_;
goto _start;
}
}
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
lean_dec(v___x_4583_);
v___x_4594_ = lean_array_get_size(v_fst_4554_);
v___x_4595_ = lean_unsigned_to_nat(0u);
v___x_4596_ = lean_nat_dec_eq(v___x_4594_, v___x_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
lean_del_object(v___x_4578_);
lean_del_object(v___x_4556_);
lean_dec(v_fst_4554_);
lean_dec_ref(v___x_4550_);
lean_dec(v_snd_4544_);
v___x_4597_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4598_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4597_, v___y_4502_, v_snd_4576_);
v___y_4510_ = v___x_4598_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4600_; 
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 1, v_snd_4544_);
lean_ctor_set(v___x_4578_, 0, v_fst_4554_);
v___x_4600_ = v___x_4578_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_fst_4554_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_snd_4544_);
v___x_4600_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4602_; 
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 1, v___x_4600_);
lean_ctor_set(v___x_4556_, 0, v___x_4550_);
v___x_4602_ = v___x_4556_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
v_as_x27_4500_ = v_tail_4508_;
v_b_4501_ = v___x_4602_;
v___y_4503_ = v_snd_4576_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_del_object(v___x_4556_);
lean_dec(v_fst_4554_);
lean_dec_ref(v___x_4550_);
lean_dec(v_snd_4544_);
v_a_4608_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4574_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4574_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_dec_ref(v___x_4550_);
lean_dec_ref(v_toConstantVal_4548_);
lean_dec(v_snd_4544_);
v_a_4619_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4551_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4551_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
v___jp_4627_:
{
lean_object* v___x_4629_; uint8_t v_isUnsafe_4630_; 
v___x_4629_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4628_);
lean_dec_ref(v___y_4628_);
v_isUnsafe_4630_ = lean_ctor_get_uint8(v___x_4629_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4630_ == 0)
{
uint8_t v___x_4631_; 
v___x_4631_ = 1;
v___y_4546_ = v___x_4629_;
v___y_4547_ = v___x_4631_;
goto v___jp_4545_;
}
else
{
if (v___x_4498_ == 0)
{
uint8_t v_exportUnsafe_4632_; 
v_exportUnsafe_4632_ = lean_ctor_get_uint8(v___y_4503_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4632_ == 0)
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
lean_dec_ref(v___x_4629_);
lean_dec(v_snd_4544_);
lean_dec(v_fst_4543_);
lean_dec(v_fst_4542_);
v___x_4633_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4634_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4633_, v___y_4502_, v___y_4503_);
v___y_4510_ = v___x_4634_;
goto v___jp_4509_;
}
else
{
v___y_4546_ = v___x_4629_;
v___y_4547_ = v_exportUnsafe_4632_;
goto v___jp_4545_;
}
}
else
{
v___y_4546_ = v___x_4629_;
v___y_4547_ = v___x_4498_;
goto v___jp_4545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object* v_as_4639_, size_t v_sz_4640_, size_t v_i_4641_, lean_object* v_b_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
uint8_t v___x_4646_; 
v___x_4646_ = lean_usize_dec_lt(v_i_4641_, v_sz_4640_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4647_, 0, v_b_4642_);
lean_ctor_set(v___x_4647_, 1, v___y_4644_);
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
else
{
lean_object* v_visitedNames_4649_; lean_object* v_visitedLevels_4650_; lean_object* v_visitedExprs_4651_; lean_object* v_visitedConstants_4652_; lean_object* v_noMDataExprs_4653_; uint8_t v_exportMData_4654_; uint8_t v_exportUnsafe_4655_; uint8_t v_ignoreMissing_4656_; lean_object* v_recursorMap_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4676_; 
v_visitedNames_4649_ = lean_ctor_get(v___y_4644_, 0);
v_visitedLevels_4650_ = lean_ctor_get(v___y_4644_, 1);
v_visitedExprs_4651_ = lean_ctor_get(v___y_4644_, 2);
v_visitedConstants_4652_ = lean_ctor_get(v___y_4644_, 3);
v_noMDataExprs_4653_ = lean_ctor_get(v___y_4644_, 4);
v_exportMData_4654_ = lean_ctor_get_uint8(v___y_4644_, sizeof(void*)*6);
v_exportUnsafe_4655_ = lean_ctor_get_uint8(v___y_4644_, sizeof(void*)*6 + 1);
v_ignoreMissing_4656_ = lean_ctor_get_uint8(v___y_4644_, sizeof(void*)*6 + 2);
v_recursorMap_4657_ = lean_ctor_get(v___y_4644_, 5);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___y_4644_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4659_ = v___y_4644_;
v_isShared_4660_ = v_isSharedCheck_4676_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_recursorMap_4657_);
lean_inc(v_noMDataExprs_4653_);
lean_inc(v_visitedConstants_4652_);
lean_inc(v_visitedExprs_4651_);
lean_inc(v_visitedLevels_4650_);
lean_inc(v_visitedNames_4649_);
lean_dec(v___y_4644_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4676_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v_a_4661_; lean_object* v_toConstantVal_4662_; lean_object* v_name_4663_; lean_object* v_type_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
v_a_4661_ = lean_array_uget_borrowed(v_as_4639_, v_i_4641_);
v_toConstantVal_4662_ = lean_ctor_get(v_a_4661_, 0);
v_name_4663_ = lean_ctor_get(v_toConstantVal_4662_, 0);
v_type_4664_ = lean_ctor_get(v_toConstantVal_4662_, 2);
v___x_4665_ = lean_box(0);
lean_inc(v_name_4663_);
v___x_4666_ = l_Lean_NameHashSet_insert(v_visitedConstants_4652_, v_name_4663_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 3, v___x_4666_);
v___x_4668_ = v___x_4659_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_visitedNames_4649_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_visitedLevels_4650_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_visitedExprs_4651_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4675_, 4, v_noMDataExprs_4653_);
lean_ctor_set(v_reuseFailAlloc_4675_, 5, v_recursorMap_4657_);
lean_ctor_set_uint8(v_reuseFailAlloc_4675_, sizeof(void*)*6, v_exportMData_4654_);
lean_ctor_set_uint8(v_reuseFailAlloc_4675_, sizeof(void*)*6 + 1, v_exportUnsafe_4655_);
lean_ctor_set_uint8(v_reuseFailAlloc_4675_, sizeof(void*)*6 + 2, v_ignoreMissing_4656_);
v___x_4668_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4669_; 
lean_inc_ref(v_type_4664_);
v___x_4669_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4664_, v___y_4643_, v___x_4668_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v_snd_4671_; size_t v___x_4672_; size_t v___x_4673_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
v_snd_4671_ = lean_ctor_get(v_a_4670_, 1);
lean_inc(v_snd_4671_);
lean_dec(v_a_4670_);
v___x_4672_ = ((size_t)1ULL);
v___x_4673_ = lean_usize_add(v_i_4641_, v___x_4672_);
v_i_4641_ = v___x_4673_;
v_b_4642_ = v___x_4665_;
v___y_4644_ = v_snd_4671_;
goto _start;
}
else
{
return v___x_4669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4677_, lean_object* v_b_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
if (lean_obj_tag(v_as_x27_4677_) == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v_b_4678_);
lean_ctor_set(v___x_4682_, 1, v___y_4680_);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
else
{
lean_object* v_head_4684_; lean_object* v_tail_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v_head_4684_ = lean_ctor_get(v_as_x27_4677_, 0);
v_tail_4685_ = lean_ctor_get(v_as_x27_4677_, 1);
v___x_4686_ = lean_box(0);
lean_inc(v_head_4684_);
v___x_4687_ = l_LeanExport_dumpConstant(v_head_4684_, v___y_4679_, v___y_4680_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v_snd_4689_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
v_snd_4689_ = lean_ctor_get(v_a_4688_, 1);
lean_inc(v_snd_4689_);
lean_dec(v_a_4688_);
v_as_x27_4677_ = v_tail_4685_;
v_b_4678_ = v___x_4686_;
v___y_4680_ = v_snd_4689_;
goto _start;
}
else
{
return v___x_4687_;
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v_fst_4703_; lean_object* v_snd_4704_; uint8_t v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = 0;
lean_inc(v_c_4691_);
lean_inc_ref(v_a_4692_);
v___x_4802_ = l_Lean_Environment_find_x3f(v_a_4692_, v_c_4691_, v___x_4801_);
if (lean_obj_tag(v___x_4802_) == 1)
{
lean_object* v_val_4803_; uint8_t v___y_5542_; uint8_t v___x_5543_; 
v_val_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_val_4803_);
lean_dec_ref_known(v___x_4802_, 1);
v___x_5543_ = l_Lean_ConstantInfo_isUnsafe(v_val_4803_);
if (v___x_5543_ == 0)
{
v___y_5542_ = v___x_5543_;
goto v___jp_5541_;
}
else
{
uint8_t v_exportUnsafe_5544_; 
v_exportUnsafe_5544_ = lean_ctor_get_uint8(v_a_4693_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5544_ == 0)
{
v___y_5542_ = v___x_5543_;
goto v___jp_5541_;
}
else
{
goto v___jp_4804_;
}
}
v___jp_4804_:
{
lean_object* v_visitedNames_4805_; lean_object* v_visitedLevels_4806_; lean_object* v_visitedExprs_4807_; lean_object* v_visitedConstants_4808_; lean_object* v_noMDataExprs_4809_; uint8_t v_exportMData_4810_; uint8_t v_exportUnsafe_4811_; uint8_t v_ignoreMissing_4812_; lean_object* v_recursorMap_4813_; uint8_t v___x_4814_; 
v_visitedNames_4805_ = lean_ctor_get(v_a_4693_, 0);
v_visitedLevels_4806_ = lean_ctor_get(v_a_4693_, 1);
v_visitedExprs_4807_ = lean_ctor_get(v_a_4693_, 2);
v_visitedConstants_4808_ = lean_ctor_get(v_a_4693_, 3);
v_noMDataExprs_4809_ = lean_ctor_get(v_a_4693_, 4);
v_exportMData_4810_ = lean_ctor_get_uint8(v_a_4693_, sizeof(void*)*6);
v_exportUnsafe_4811_ = lean_ctor_get_uint8(v_a_4693_, sizeof(void*)*6 + 1);
v_ignoreMissing_4812_ = lean_ctor_get_uint8(v_a_4693_, sizeof(void*)*6 + 2);
v_recursorMap_4813_ = lean_ctor_get(v_a_4693_, 5);
v___x_4814_ = l_Lean_NameHashSet_contains(v_visitedConstants_4808_, v_c_4691_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_5534_; 
lean_inc(v_recursorMap_4813_);
lean_inc_ref(v_noMDataExprs_4809_);
lean_inc_ref(v_visitedConstants_4808_);
lean_inc_ref(v_visitedExprs_4807_);
lean_inc_ref(v_visitedLevels_4806_);
lean_inc_ref(v_visitedNames_4805_);
v_isSharedCheck_5534_ = !lean_is_exclusive(v_a_4693_);
if (v_isSharedCheck_5534_ == 0)
{
lean_object* v_unused_5535_; lean_object* v_unused_5536_; lean_object* v_unused_5537_; lean_object* v_unused_5538_; lean_object* v_unused_5539_; lean_object* v_unused_5540_; 
v_unused_5535_ = lean_ctor_get(v_a_4693_, 5);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_a_4693_, 4);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_a_4693_, 3);
lean_dec(v_unused_5537_);
v_unused_5538_ = lean_ctor_get(v_a_4693_, 2);
lean_dec(v_unused_5538_);
v_unused_5539_ = lean_ctor_get(v_a_4693_, 1);
lean_dec(v_unused_5539_);
v_unused_5540_ = lean_ctor_get(v_a_4693_, 0);
lean_dec(v_unused_5540_);
v___x_4816_ = v_a_4693_;
v_isShared_4817_ = v_isSharedCheck_5534_;
goto v_resetjp_4815_;
}
else
{
lean_dec(v_a_4693_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_5534_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4818_ = l_Lean_NameHashSet_insert(v_visitedConstants_4808_, v_c_4691_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 3, v___x_4818_);
v___x_4820_ = v___x_4816_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_visitedNames_4805_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_visitedLevels_4806_);
lean_ctor_set(v_reuseFailAlloc_5533_, 2, v_visitedExprs_4807_);
lean_ctor_set(v_reuseFailAlloc_5533_, 3, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_5533_, 4, v_noMDataExprs_4809_);
lean_ctor_set(v_reuseFailAlloc_5533_, 5, v_recursorMap_4813_);
lean_ctor_set_uint8(v_reuseFailAlloc_5533_, sizeof(void*)*6, v_exportMData_4810_);
lean_ctor_set_uint8(v_reuseFailAlloc_5533_, sizeof(void*)*6 + 1, v_exportUnsafe_4811_);
lean_ctor_set_uint8(v_reuseFailAlloc_5533_, sizeof(void*)*6 + 2, v_ignoreMissing_4812_);
v___x_4820_ = v_reuseFailAlloc_5533_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
switch(lean_obj_tag(v_val_4803_))
{
case 0:
{
lean_object* v_val_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4925_; 
v_val_4821_ = lean_ctor_get(v_val_4803_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_val_4803_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4823_ = v_val_4803_;
v_isShared_4824_ = v_isSharedCheck_4925_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_val_4821_);
lean_dec(v_val_4803_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4925_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v_toConstantVal_4825_; uint8_t v_isUnsafe_4826_; lean_object* v_name_4827_; lean_object* v_levelParams_4828_; lean_object* v_type_4829_; lean_object* v___x_4830_; 
v_toConstantVal_4825_ = lean_ctor_get(v_val_4821_, 0);
lean_inc_ref(v_toConstantVal_4825_);
v_isUnsafe_4826_ = lean_ctor_get_uint8(v_val_4821_, sizeof(void*)*1);
lean_dec_ref(v_val_4821_);
v_name_4827_ = lean_ctor_get(v_toConstantVal_4825_, 0);
lean_inc(v_name_4827_);
v_levelParams_4828_ = lean_ctor_get(v_toConstantVal_4825_, 1);
lean_inc(v_levelParams_4828_);
v_type_4829_ = lean_ctor_get(v_toConstantVal_4825_, 2);
lean_inc_ref_n(v_type_4829_, 2);
lean_dec_ref(v_toConstantVal_4825_);
v___x_4830_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4829_, v_a_4692_, v___x_4820_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4924_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4924_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4924_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_snd_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4922_; 
v_snd_4835_ = lean_ctor_get(v_a_4831_, 1);
v_isSharedCheck_4922_ = !lean_is_exclusive(v_a_4831_);
if (v_isSharedCheck_4922_ == 0)
{
lean_object* v_unused_4923_; 
v_unused_4923_ = lean_ctor_get(v_a_4831_, 0);
lean_dec(v_unused_4923_);
v___x_4837_ = v_a_4831_;
v_isShared_4838_ = v_isSharedCheck_4922_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_snd_4835_);
lean_dec(v_a_4831_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4922_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; 
v___x_4839_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4827_, v_a_4692_, v_snd_4835_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v_fst_4841_; lean_object* v_snd_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4913_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref_known(v___x_4839_, 1);
v_fst_4841_ = lean_ctor_get(v_a_4840_, 0);
v_snd_4842_ = lean_ctor_get(v_a_4840_, 1);
v_isSharedCheck_4913_ = !lean_is_exclusive(v_a_4840_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4844_ = v_a_4840_;
v_isShared_4845_ = v_isSharedCheck_4913_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_snd_4842_);
lean_inc(v_fst_4841_);
lean_dec(v_a_4840_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4913_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; 
v___x_4846_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4828_, v_a_4692_, v_snd_4842_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v_fst_4848_; lean_object* v_snd_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4904_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4846_, 1);
v_fst_4848_ = lean_ctor_get(v_a_4847_, 0);
v_snd_4849_ = lean_ctor_get(v_a_4847_, 1);
v_isSharedCheck_4904_ = !lean_is_exclusive(v_a_4847_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4851_ = v_a_4847_;
v_isShared_4852_ = v_isSharedCheck_4904_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_snd_4849_);
lean_inc(v_fst_4848_);
lean_dec(v_a_4847_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4904_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_LeanExport_dumpExpr(v_type_4829_, v_a_4692_, v_snd_4849_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v_fst_4855_; lean_object* v_snd_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4895_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___x_4853_, 1);
v_fst_4855_ = lean_ctor_get(v_a_4854_, 0);
v_snd_4856_ = lean_ctor_get(v_a_4854_, 1);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_a_4854_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4858_ = v_a_4854_;
v_isShared_4859_ = v_isSharedCheck_4895_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_snd_4856_);
lean_inc(v_fst_4855_);
lean_dec(v_a_4854_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4895_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4864_; 
v___x_4860_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_4861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4862_ = l_Lean_JsonNumber_fromNat(v_fst_4841_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set_tag(v___x_4833_, 2);
lean_ctor_set(v___x_4833_, 0, v___x_4862_);
v___x_4864_ = v___x_4833_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4862_);
v___x_4864_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
lean_object* v___x_4866_; 
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 1, v___x_4864_);
lean_ctor_set(v___x_4858_, 0, v___x_4861_);
v___x_4866_ = v___x_4858_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4869_; 
v___x_4867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 1, v_fst_4848_);
lean_ctor_set(v___x_4851_, 0, v___x_4867_);
v___x_4869_ = v___x_4851_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4867_);
lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_fst_4848_);
v___x_4869_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4870_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4871_ = l_Lean_JsonNumber_fromNat(v_fst_4855_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set_tag(v___x_4823_, 2);
lean_ctor_set(v___x_4823_, 0, v___x_4871_);
v___x_4873_ = v___x_4823_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4875_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 1, v___x_4873_);
lean_ctor_set(v___x_4844_, 0, v___x_4870_);
v___x_4875_ = v___x_4844_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4870_);
lean_ctor_set(v_reuseFailAlloc_4890_, 1, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4877_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4877_, 0, v_isUnsafe_4826_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 1, v___x_4877_);
lean_ctor_set(v___x_4837_, 0, v___x_4876_);
v___x_4879_ = v___x_4837_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4880_ = lean_box(0);
v___x_4881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4875_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
v___x_4883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4869_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4866_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l_Lean_Json_mkObj(v___x_4884_);
lean_dec_ref_known(v___x_4884_, 2);
v___x_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4860_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4880_);
v___x_4888_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4887_, v_snd_4856_);
lean_dec_ref_known(v___x_4887_, 2);
return v___x_4888_;
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
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_del_object(v___x_4851_);
lean_dec(v_fst_4848_);
lean_del_object(v___x_4844_);
lean_dec(v_fst_4841_);
lean_del_object(v___x_4837_);
lean_del_object(v___x_4833_);
lean_del_object(v___x_4823_);
v_a_4896_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4853_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4853_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_del_object(v___x_4844_);
lean_dec(v_fst_4841_);
lean_del_object(v___x_4837_);
lean_del_object(v___x_4833_);
lean_dec_ref(v_type_4829_);
lean_del_object(v___x_4823_);
v_a_4905_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4846_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4846_);
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
lean_del_object(v___x_4837_);
lean_del_object(v___x_4833_);
lean_dec_ref(v_type_4829_);
lean_dec(v_levelParams_4828_);
lean_del_object(v___x_4823_);
v_a_4914_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4839_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4839_);
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
}
else
{
lean_dec_ref(v_type_4829_);
lean_dec(v_levelParams_4828_);
lean_dec(v_name_4827_);
lean_del_object(v___x_4823_);
return v___x_4830_;
}
}
}
case 1:
{
lean_object* v_val_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_5097_; 
v_val_4926_ = lean_ctor_get(v_val_4803_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v_val_4803_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_4928_ = v_val_4803_;
v_isShared_4929_ = v_isSharedCheck_5097_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_val_4926_);
lean_dec(v_val_4803_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_5097_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_toConstantVal_4930_; lean_object* v_value_4931_; lean_object* v_hints_4932_; uint8_t v_safety_4933_; lean_object* v_all_4934_; lean_object* v_name_4935_; lean_object* v_levelParams_4936_; lean_object* v_type_4937_; lean_object* v___x_4938_; 
v_toConstantVal_4930_ = lean_ctor_get(v_val_4926_, 0);
lean_inc_ref(v_toConstantVal_4930_);
v_value_4931_ = lean_ctor_get(v_val_4926_, 1);
lean_inc_ref(v_value_4931_);
v_hints_4932_ = lean_ctor_get(v_val_4926_, 2);
lean_inc(v_hints_4932_);
v_safety_4933_ = lean_ctor_get_uint8(v_val_4926_, sizeof(void*)*4);
v_all_4934_ = lean_ctor_get(v_val_4926_, 3);
lean_inc(v_all_4934_);
lean_dec_ref(v_val_4926_);
v_name_4935_ = lean_ctor_get(v_toConstantVal_4930_, 0);
lean_inc(v_name_4935_);
v_levelParams_4936_ = lean_ctor_get(v_toConstantVal_4930_, 1);
lean_inc(v_levelParams_4936_);
v_type_4937_ = lean_ctor_get(v_toConstantVal_4930_, 2);
lean_inc_ref_n(v_type_4937_, 2);
lean_dec_ref(v_toConstantVal_4930_);
v___x_4938_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4937_, v_a_4692_, v___x_4820_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5096_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_4941_ = v___x_4938_;
v_isShared_4942_ = v_isSharedCheck_5096_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5096_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v_snd_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_5094_; 
v_snd_4943_ = lean_ctor_get(v_a_4939_, 1);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_a_4939_);
if (v_isSharedCheck_5094_ == 0)
{
lean_object* v_unused_5095_; 
v_unused_5095_ = lean_ctor_get(v_a_4939_, 0);
lean_dec(v_unused_5095_);
v___x_4945_ = v_a_4939_;
v_isShared_4946_ = v_isSharedCheck_5094_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_snd_4943_);
lean_dec(v_a_4939_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_5094_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4947_; 
lean_inc_ref(v_value_4931_);
v___x_4947_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_4931_, v_a_4692_, v_snd_4943_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5093_; 
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_5093_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5093_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v_snd_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_5091_; 
v_snd_4952_ = lean_ctor_get(v_a_4948_, 1);
v_isSharedCheck_5091_ = !lean_is_exclusive(v_a_4948_);
if (v_isSharedCheck_5091_ == 0)
{
lean_object* v_unused_5092_; 
v_unused_5092_ = lean_ctor_get(v_a_4948_, 0);
lean_dec(v_unused_5092_);
v___x_4954_ = v_a_4948_;
v_isShared_4955_ = v_isSharedCheck_5091_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_snd_4952_);
lean_dec(v_a_4948_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_5091_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4956_; 
v___x_4956_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4935_, v_a_4692_, v_snd_4952_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v_fst_4958_; lean_object* v_snd_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_5082_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v_fst_4958_ = lean_ctor_get(v_a_4957_, 0);
v_snd_4959_ = lean_ctor_get(v_a_4957_, 1);
v_isSharedCheck_5082_ = !lean_is_exclusive(v_a_4957_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_4961_ = v_a_4957_;
v_isShared_4962_ = v_isSharedCheck_5082_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_snd_4959_);
lean_inc(v_fst_4958_);
lean_dec(v_a_4957_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_5082_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4963_; 
v___x_4963_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4936_, v_a_4692_, v_snd_4959_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v_fst_4965_; lean_object* v_snd_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5073_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v_fst_4965_ = lean_ctor_get(v_a_4964_, 0);
v_snd_4966_ = lean_ctor_get(v_a_4964_, 1);
v_isSharedCheck_5073_ = !lean_is_exclusive(v_a_4964_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_4968_ = v_a_4964_;
v_isShared_4969_ = v_isSharedCheck_5073_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_snd_4966_);
lean_inc(v_fst_4965_);
lean_dec(v_a_4964_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5073_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_LeanExport_dumpExpr(v_type_4937_, v_a_4692_, v_snd_4966_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v_fst_4972_; lean_object* v_snd_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_5064_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
v_fst_4972_ = lean_ctor_get(v_a_4971_, 0);
v_snd_4973_ = lean_ctor_get(v_a_4971_, 1);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_a_4971_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_4975_ = v_a_4971_;
v_isShared_4976_ = v_isSharedCheck_5064_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_snd_4973_);
lean_inc(v_fst_4972_);
lean_dec(v_a_4971_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_5064_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4977_; 
v___x_4977_ = l_LeanExport_dumpExpr(v_value_4931_, v_a_4692_, v_snd_4973_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v_fst_4979_; lean_object* v_snd_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_5055_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v_fst_4979_ = lean_ctor_get(v_a_4978_, 0);
v_snd_4980_ = lean_ctor_get(v_a_4978_, 1);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_a_4978_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_4982_ = v_a_4978_;
v_isShared_4983_ = v_isSharedCheck_5055_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_snd_4980_);
lean_inc(v_fst_4979_);
lean_dec(v_a_4978_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_5055_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; 
v___x_4984_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4934_, v_a_4692_, v_snd_4980_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v_fst_4986_; lean_object* v_snd_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5046_; 
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4984_, 1);
v_fst_4986_ = lean_ctor_get(v_a_4985_, 0);
v_snd_4987_ = lean_ctor_get(v_a_4985_, 1);
v_isSharedCheck_5046_ = !lean_is_exclusive(v_a_4985_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_4989_ = v_a_4985_;
v_isShared_4990_ = v_isSharedCheck_5046_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_snd_4987_);
lean_inc(v_fst_4986_);
lean_dec(v_a_4985_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5046_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4995_; 
v___x_4991_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_4992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4993_ = l_Lean_JsonNumber_fromNat(v_fst_4958_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set_tag(v___x_4950_, 2);
lean_ctor_set(v___x_4950_, 0, v___x_4993_);
v___x_4995_ = v___x_4950_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_4993_);
v___x_4995_ = v_reuseFailAlloc_5045_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4997_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_4995_);
lean_ctor_set(v___x_4989_, 0, v___x_4992_);
v___x_4997_ = v___x_4989_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_5044_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 1, v_fst_4965_);
lean_ctor_set(v___x_4982_, 0, v___x_4998_);
v___x_5000_ = v___x_4982_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_4998_);
lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_fst_4965_);
v___x_5000_ = v_reuseFailAlloc_5043_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_5001_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5002_ = l_Lean_JsonNumber_fromNat(v_fst_4972_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set_tag(v___x_4941_, 2);
lean_ctor_set(v___x_4941_, 0, v___x_5002_);
v___x_5004_ = v___x_4941_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5006_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 1, v___x_5004_);
lean_ctor_set(v___x_4975_, 0, v___x_5001_);
v___x_5006_ = v___x_4975_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5001_);
lean_ctor_set(v_reuseFailAlloc_5041_, 1, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5010_; 
v___x_5007_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5008_ = l_Lean_JsonNumber_fromNat(v_fst_4979_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set_tag(v___x_4928_, 2);
lean_ctor_set(v___x_4928_, 0, v___x_5008_);
v___x_5010_ = v___x_4928_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5012_; 
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 1, v___x_5010_);
lean_ctor_set(v___x_4968_, 0, v___x_5007_);
v___x_5012_ = v___x_4968_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5007_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v___x_5010_);
v___x_5012_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5013_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_5014_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_4932_);
lean_dec(v_hints_4932_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_5014_);
lean_ctor_set(v___x_4961_, 0, v___x_5013_);
v___x_5016_ = v___x_4961_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5017_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_5018_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_4933_);
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 1, v___x_5018_);
lean_ctor_set(v___x_4954_, 0, v___x_5017_);
v___x_5020_ = v___x_4954_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5017_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v_fst_4986_);
lean_ctor_set(v___x_4945_, 0, v___x_5021_);
v___x_5023_ = v___x_4945_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5021_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_fst_4986_);
v___x_5023_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5024_ = lean_box(0);
v___x_5025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5023_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5020_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
v___x_5027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5016_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
v___x_5028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5028_, 0, v___x_5012_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
v___x_5029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5006_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
v___x_5030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5000_);
lean_ctor_set(v___x_5030_, 1, v___x_5029_);
v___x_5031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_4997_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
v___x_5032_ = l_Lean_Json_mkObj(v___x_5031_);
lean_dec_ref_known(v___x_5031_, 2);
v___x_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_4991_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
lean_ctor_set(v___x_5034_, 1, v___x_5024_);
v___x_5035_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5034_, v_snd_4987_);
lean_dec_ref_known(v___x_5034_, 2);
return v___x_5035_;
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
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_del_object(v___x_4982_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4975_);
lean_dec(v_fst_4972_);
lean_del_object(v___x_4968_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_hints_4932_);
lean_del_object(v___x_4928_);
v_a_5047_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_4984_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_4984_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_del_object(v___x_4975_);
lean_dec(v_fst_4972_);
lean_del_object(v___x_4968_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_del_object(v___x_4928_);
v_a_5056_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_4977_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_4977_);
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
lean_del_object(v___x_4968_);
lean_dec(v_fst_4965_);
lean_del_object(v___x_4961_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_dec_ref(v_value_4931_);
lean_del_object(v___x_4928_);
v_a_5065_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_4970_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_4970_);
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
lean_del_object(v___x_4961_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec_ref(v_type_4937_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_dec_ref(v_value_4931_);
lean_del_object(v___x_4928_);
v_a_5074_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5076_ = v___x_4963_;
v_isShared_5077_ = v_isSharedCheck_5081_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_4963_);
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
lean_del_object(v___x_4954_);
lean_del_object(v___x_4950_);
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec_ref(v_type_4937_);
lean_dec(v_levelParams_4936_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_dec_ref(v_value_4931_);
lean_del_object(v___x_4928_);
v_a_5083_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_4956_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_4956_);
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
}
else
{
lean_del_object(v___x_4945_);
lean_del_object(v___x_4941_);
lean_dec_ref(v_type_4937_);
lean_dec(v_levelParams_4936_);
lean_dec(v_name_4935_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_dec_ref(v_value_4931_);
lean_del_object(v___x_4928_);
return v___x_4947_;
}
}
}
}
else
{
lean_dec_ref(v_type_4937_);
lean_dec(v_levelParams_4936_);
lean_dec(v_name_4935_);
lean_dec(v_all_4934_);
lean_dec(v_hints_4932_);
lean_dec_ref(v_value_4931_);
lean_del_object(v___x_4928_);
return v___x_4938_;
}
}
}
case 2:
{
lean_object* v_val_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5259_; 
v_val_5098_ = lean_ctor_get(v_val_4803_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v_val_4803_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5100_ = v_val_4803_;
v_isShared_5101_ = v_isSharedCheck_5259_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_val_5098_);
lean_dec(v_val_4803_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5259_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v_toConstantVal_5102_; lean_object* v_value_5103_; lean_object* v_all_5104_; lean_object* v_name_5105_; lean_object* v_levelParams_5106_; lean_object* v_type_5107_; lean_object* v___x_5108_; 
v_toConstantVal_5102_ = lean_ctor_get(v_val_5098_, 0);
lean_inc_ref(v_toConstantVal_5102_);
v_value_5103_ = lean_ctor_get(v_val_5098_, 1);
lean_inc_ref(v_value_5103_);
v_all_5104_ = lean_ctor_get(v_val_5098_, 2);
lean_inc(v_all_5104_);
lean_dec_ref(v_val_5098_);
v_name_5105_ = lean_ctor_get(v_toConstantVal_5102_, 0);
lean_inc(v_name_5105_);
v_levelParams_5106_ = lean_ctor_get(v_toConstantVal_5102_, 1);
lean_inc(v_levelParams_5106_);
v_type_5107_ = lean_ctor_get(v_toConstantVal_5102_, 2);
lean_inc_ref_n(v_type_5107_, 2);
lean_dec_ref(v_toConstantVal_5102_);
v___x_5108_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5107_, v_a_4692_, v___x_4820_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5258_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5111_ = v___x_5108_;
v_isShared_5112_ = v_isSharedCheck_5258_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5108_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5258_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v_snd_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5256_; 
v_snd_5113_ = lean_ctor_get(v_a_5109_, 1);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_a_5109_);
if (v_isSharedCheck_5256_ == 0)
{
lean_object* v_unused_5257_; 
v_unused_5257_ = lean_ctor_get(v_a_5109_, 0);
lean_dec(v_unused_5257_);
v___x_5115_ = v_a_5109_;
v_isShared_5116_ = v_isSharedCheck_5256_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_snd_5113_);
lean_dec(v_a_5109_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5256_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; 
lean_inc_ref(v_value_5103_);
v___x_5117_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5103_, v_a_4692_, v_snd_5113_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5255_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5120_ = v___x_5117_;
v_isShared_5121_ = v_isSharedCheck_5255_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5117_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5255_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v_snd_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5253_; 
v_snd_5122_ = lean_ctor_get(v_a_5118_, 1);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_a_5118_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v_a_5118_, 0);
lean_dec(v_unused_5254_);
v___x_5124_ = v_a_5118_;
v_isShared_5125_ = v_isSharedCheck_5253_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_snd_5122_);
lean_dec(v_a_5118_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5253_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; 
v___x_5126_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5105_, v_a_4692_, v_snd_5122_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v_fst_5128_; lean_object* v_snd_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5244_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5126_, 1);
v_fst_5128_ = lean_ctor_get(v_a_5127_, 0);
v_snd_5129_ = lean_ctor_get(v_a_5127_, 1);
v_isSharedCheck_5244_ = !lean_is_exclusive(v_a_5127_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5131_ = v_a_5127_;
v_isShared_5132_ = v_isSharedCheck_5244_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_snd_5129_);
lean_inc(v_fst_5128_);
lean_dec(v_a_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5244_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; 
v___x_5133_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5106_, v_a_4692_, v_snd_5129_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v_fst_5135_; lean_object* v_snd_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5235_; 
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_a_5134_);
lean_dec_ref_known(v___x_5133_, 1);
v_fst_5135_ = lean_ctor_get(v_a_5134_, 0);
v_snd_5136_ = lean_ctor_get(v_a_5134_, 1);
v_isSharedCheck_5235_ = !lean_is_exclusive(v_a_5134_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5138_ = v_a_5134_;
v_isShared_5139_ = v_isSharedCheck_5235_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_snd_5136_);
lean_inc(v_fst_5135_);
lean_dec(v_a_5134_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5235_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_LeanExport_dumpExpr(v_type_5107_, v_a_4692_, v_snd_5136_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v_fst_5142_; lean_object* v_snd_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5226_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5140_, 1);
v_fst_5142_ = lean_ctor_get(v_a_5141_, 0);
v_snd_5143_ = lean_ctor_get(v_a_5141_, 1);
v_isSharedCheck_5226_ = !lean_is_exclusive(v_a_5141_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5145_ = v_a_5141_;
v_isShared_5146_ = v_isSharedCheck_5226_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_snd_5143_);
lean_inc(v_fst_5142_);
lean_dec(v_a_5141_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5226_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_LeanExport_dumpExpr(v_value_5103_, v_a_4692_, v_snd_5143_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v_fst_5149_; lean_object* v_snd_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5217_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v_fst_5149_ = lean_ctor_get(v_a_5148_, 0);
v_snd_5150_ = lean_ctor_get(v_a_5148_, 1);
v_isSharedCheck_5217_ = !lean_is_exclusive(v_a_5148_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5152_ = v_a_5148_;
v_isShared_5153_ = v_isSharedCheck_5217_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_snd_5150_);
lean_inc(v_fst_5149_);
lean_dec(v_a_5148_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5217_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5154_; 
v___x_5154_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5104_, v_a_4692_, v_snd_5150_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v_fst_5156_; lean_object* v_snd_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5208_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5154_, 1);
v_fst_5156_ = lean_ctor_get(v_a_5155_, 0);
v_snd_5157_ = lean_ctor_get(v_a_5155_, 1);
v_isSharedCheck_5208_ = !lean_is_exclusive(v_a_5155_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5159_ = v_a_5155_;
v_isShared_5160_ = v_isSharedCheck_5208_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_snd_5157_);
lean_inc(v_fst_5156_);
lean_dec(v_a_5155_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5208_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5165_; 
v___x_5161_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5163_ = l_Lean_JsonNumber_fromNat(v_fst_5128_);
if (v_isShared_5121_ == 0)
{
lean_ctor_set_tag(v___x_5120_, 2);
lean_ctor_set(v___x_5120_, 0, v___x_5163_);
v___x_5165_ = v___x_5120_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5167_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 1, v___x_5165_);
lean_ctor_set(v___x_5159_, 0, v___x_5162_);
v___x_5167_ = v___x_5159_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5206_, 1, v___x_5165_);
v___x_5167_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 1, v_fst_5135_);
lean_ctor_set(v___x_5152_, 0, v___x_5168_);
v___x_5170_ = v___x_5152_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v___x_5168_);
lean_ctor_set(v_reuseFailAlloc_5205_, 1, v_fst_5135_);
v___x_5170_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5174_; 
v___x_5171_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5172_ = l_Lean_JsonNumber_fromNat(v_fst_5142_);
if (v_isShared_5112_ == 0)
{
lean_ctor_set_tag(v___x_5111_, 2);
lean_ctor_set(v___x_5111_, 0, v___x_5172_);
v___x_5174_ = v___x_5111_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5172_);
v___x_5174_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5176_; 
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 1, v___x_5174_);
lean_ctor_set(v___x_5145_, 0, v___x_5171_);
v___x_5176_ = v___x_5145_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5203_, 1, v___x_5174_);
v___x_5176_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5180_; 
v___x_5177_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5178_ = l_Lean_JsonNumber_fromNat(v_fst_5149_);
if (v_isShared_5101_ == 0)
{
lean_ctor_set(v___x_5100_, 0, v___x_5178_);
v___x_5180_ = v___x_5100_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5178_);
v___x_5180_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5182_; 
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 1, v___x_5180_);
lean_ctor_set(v___x_5138_, 0, v___x_5177_);
v___x_5182_ = v___x_5138_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5201_, 1, v___x_5180_);
v___x_5182_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 1, v_fst_5156_);
lean_ctor_set(v___x_5131_, 0, v___x_5183_);
v___x_5185_ = v___x_5131_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5183_);
lean_ctor_set(v_reuseFailAlloc_5200_, 1, v_fst_5156_);
v___x_5185_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
lean_object* v___x_5186_; lean_object* v___x_5188_; 
v___x_5186_ = lean_box(0);
if (v_isShared_5116_ == 0)
{
lean_ctor_set_tag(v___x_5115_, 1);
lean_ctor_set(v___x_5115_, 1, v___x_5186_);
lean_ctor_set(v___x_5115_, 0, v___x_5185_);
v___x_5188_ = v___x_5115_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v___x_5185_);
lean_ctor_set(v_reuseFailAlloc_5199_, 1, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5195_; 
v___x_5189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5182_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
v___x_5190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5176_);
lean_ctor_set(v___x_5190_, 1, v___x_5189_);
v___x_5191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5170_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5167_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l_Lean_Json_mkObj(v___x_5192_);
lean_dec_ref_known(v___x_5192_, 2);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 1, v___x_5193_);
lean_ctor_set(v___x_5124_, 0, v___x_5161_);
v___x_5195_ = v___x_5124_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5198_, 1, v___x_5193_);
v___x_5195_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5195_);
lean_ctor_set(v___x_5196_, 1, v___x_5186_);
v___x_5197_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5196_, v_snd_5157_);
lean_dec_ref_known(v___x_5196_, 2);
return v___x_5197_;
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
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
lean_del_object(v___x_5152_);
lean_dec(v_fst_5149_);
lean_del_object(v___x_5145_);
lean_dec(v_fst_5142_);
lean_del_object(v___x_5138_);
lean_dec(v_fst_5135_);
lean_del_object(v___x_5131_);
lean_dec(v_fst_5128_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_del_object(v___x_5100_);
v_a_5209_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5154_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5154_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_del_object(v___x_5145_);
lean_dec(v_fst_5142_);
lean_del_object(v___x_5138_);
lean_dec(v_fst_5135_);
lean_del_object(v___x_5131_);
lean_dec(v_fst_5128_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_dec(v_all_5104_);
lean_del_object(v___x_5100_);
v_a_5218_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5147_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5147_);
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
lean_del_object(v___x_5138_);
lean_dec(v_fst_5135_);
lean_del_object(v___x_5131_);
lean_dec(v_fst_5128_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_dec(v_all_5104_);
lean_dec_ref(v_value_5103_);
lean_del_object(v___x_5100_);
v_a_5227_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5140_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5140_);
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
lean_del_object(v___x_5131_);
lean_dec(v_fst_5128_);
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_dec_ref(v_type_5107_);
lean_dec(v_all_5104_);
lean_dec_ref(v_value_5103_);
lean_del_object(v___x_5100_);
v_a_5236_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5133_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5133_);
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
lean_del_object(v___x_5124_);
lean_del_object(v___x_5120_);
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_dec_ref(v_type_5107_);
lean_dec(v_levelParams_5106_);
lean_dec(v_all_5104_);
lean_dec_ref(v_value_5103_);
lean_del_object(v___x_5100_);
v_a_5245_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5126_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5126_);
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
}
else
{
lean_del_object(v___x_5115_);
lean_del_object(v___x_5111_);
lean_dec_ref(v_type_5107_);
lean_dec(v_levelParams_5106_);
lean_dec(v_name_5105_);
lean_dec(v_all_5104_);
lean_dec_ref(v_value_5103_);
lean_del_object(v___x_5100_);
return v___x_5117_;
}
}
}
}
else
{
lean_dec_ref(v_type_5107_);
lean_dec(v_levelParams_5106_);
lean_dec(v_name_5105_);
lean_dec(v_all_5104_);
lean_dec_ref(v_value_5103_);
lean_del_object(v___x_5100_);
return v___x_5108_;
}
}
}
case 3:
{
lean_object* v_val_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5426_; 
v_val_5260_ = lean_ctor_get(v_val_4803_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v_val_4803_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5262_ = v_val_4803_;
v_isShared_5263_ = v_isSharedCheck_5426_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_val_5260_);
lean_dec(v_val_4803_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5426_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v_toConstantVal_5264_; lean_object* v_value_5265_; uint8_t v_isUnsafe_5266_; lean_object* v_all_5267_; lean_object* v_name_5268_; lean_object* v_levelParams_5269_; lean_object* v_type_5270_; lean_object* v___x_5271_; 
v_toConstantVal_5264_ = lean_ctor_get(v_val_5260_, 0);
lean_inc_ref(v_toConstantVal_5264_);
v_value_5265_ = lean_ctor_get(v_val_5260_, 1);
lean_inc_ref(v_value_5265_);
v_isUnsafe_5266_ = lean_ctor_get_uint8(v_val_5260_, sizeof(void*)*3);
v_all_5267_ = lean_ctor_get(v_val_5260_, 2);
lean_inc(v_all_5267_);
lean_dec_ref(v_val_5260_);
v_name_5268_ = lean_ctor_get(v_toConstantVal_5264_, 0);
lean_inc(v_name_5268_);
v_levelParams_5269_ = lean_ctor_get(v_toConstantVal_5264_, 1);
lean_inc(v_levelParams_5269_);
v_type_5270_ = lean_ctor_get(v_toConstantVal_5264_, 2);
lean_inc_ref_n(v_type_5270_, 2);
lean_dec_ref(v_toConstantVal_5264_);
v___x_5271_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5270_, v_a_4692_, v___x_4820_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5425_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5425_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5425_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_snd_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5423_; 
v_snd_5276_ = lean_ctor_get(v_a_5272_, 1);
v_isSharedCheck_5423_ = !lean_is_exclusive(v_a_5272_);
if (v_isSharedCheck_5423_ == 0)
{
lean_object* v_unused_5424_; 
v_unused_5424_ = lean_ctor_get(v_a_5272_, 0);
lean_dec(v_unused_5424_);
v___x_5278_ = v_a_5272_;
v_isShared_5279_ = v_isSharedCheck_5423_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_snd_5276_);
lean_dec(v_a_5272_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5423_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5280_; 
lean_inc_ref(v_value_5265_);
v___x_5280_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5265_, v_a_4692_, v_snd_5276_);
if (lean_obj_tag(v___x_5280_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5422_; 
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5283_ = v___x_5280_;
v_isShared_5284_ = v_isSharedCheck_5422_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5280_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5422_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v_snd_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5420_; 
v_snd_5285_ = lean_ctor_get(v_a_5281_, 1);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_a_5281_);
if (v_isSharedCheck_5420_ == 0)
{
lean_object* v_unused_5421_; 
v_unused_5421_ = lean_ctor_get(v_a_5281_, 0);
lean_dec(v_unused_5421_);
v___x_5287_ = v_a_5281_;
v_isShared_5288_ = v_isSharedCheck_5420_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_snd_5285_);
lean_dec(v_a_5281_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5420_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; 
v___x_5289_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5268_, v_a_4692_, v_snd_5285_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v_fst_5291_; lean_object* v_snd_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5411_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_a_5290_);
lean_dec_ref_known(v___x_5289_, 1);
v_fst_5291_ = lean_ctor_get(v_a_5290_, 0);
v_snd_5292_ = lean_ctor_get(v_a_5290_, 1);
v_isSharedCheck_5411_ = !lean_is_exclusive(v_a_5290_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5294_ = v_a_5290_;
v_isShared_5295_ = v_isSharedCheck_5411_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_snd_5292_);
lean_inc(v_fst_5291_);
lean_dec(v_a_5290_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5411_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5296_; 
v___x_5296_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5269_, v_a_4692_, v_snd_5292_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; lean_object* v_fst_5298_; lean_object* v_snd_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5402_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
lean_inc(v_a_5297_);
lean_dec_ref_known(v___x_5296_, 1);
v_fst_5298_ = lean_ctor_get(v_a_5297_, 0);
v_snd_5299_ = lean_ctor_get(v_a_5297_, 1);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_a_5297_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5301_ = v_a_5297_;
v_isShared_5302_ = v_isSharedCheck_5402_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_snd_5299_);
lean_inc(v_fst_5298_);
lean_dec(v_a_5297_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5402_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5303_; 
v___x_5303_ = l_LeanExport_dumpExpr(v_type_5270_, v_a_4692_, v_snd_5299_);
if (lean_obj_tag(v___x_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v_fst_5305_; lean_object* v_snd_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5393_; 
v_a_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_a_5304_);
lean_dec_ref_known(v___x_5303_, 1);
v_fst_5305_ = lean_ctor_get(v_a_5304_, 0);
v_snd_5306_ = lean_ctor_get(v_a_5304_, 1);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_a_5304_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5308_ = v_a_5304_;
v_isShared_5309_ = v_isSharedCheck_5393_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_snd_5306_);
lean_inc(v_fst_5305_);
lean_dec(v_a_5304_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5393_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5310_; 
v___x_5310_ = l_LeanExport_dumpExpr(v_value_5265_, v_a_4692_, v_snd_5306_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v_fst_5312_; lean_object* v_snd_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5384_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
lean_inc(v_a_5311_);
lean_dec_ref_known(v___x_5310_, 1);
v_fst_5312_ = lean_ctor_get(v_a_5311_, 0);
v_snd_5313_ = lean_ctor_get(v_a_5311_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_a_5311_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5315_ = v_a_5311_;
v_isShared_5316_ = v_isSharedCheck_5384_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_snd_5313_);
lean_inc(v_fst_5312_);
lean_dec(v_a_5311_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5384_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5317_; 
v___x_5317_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5267_, v_a_4692_, v_snd_5313_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; lean_object* v_fst_5319_; lean_object* v_snd_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5375_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_a_5318_);
lean_dec_ref_known(v___x_5317_, 1);
v_fst_5319_ = lean_ctor_get(v_a_5318_, 0);
v_snd_5320_ = lean_ctor_get(v_a_5318_, 1);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_a_5318_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5322_ = v_a_5318_;
v_isShared_5323_ = v_isSharedCheck_5375_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_snd_5320_);
lean_inc(v_fst_5319_);
lean_dec(v_a_5318_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5375_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5324_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5326_ = l_Lean_JsonNumber_fromNat(v_fst_5291_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set_tag(v___x_5283_, 2);
lean_ctor_set(v___x_5283_, 0, v___x_5326_);
v___x_5328_ = v___x_5283_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5326_);
v___x_5328_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
lean_object* v___x_5330_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set(v___x_5322_, 1, v___x_5328_);
lean_ctor_set(v___x_5322_, 0, v___x_5325_);
v___x_5330_ = v___x_5322_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5325_);
lean_ctor_set(v_reuseFailAlloc_5373_, 1, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 1, v_fst_5298_);
lean_ctor_set(v___x_5315_, 0, v___x_5331_);
v___x_5333_ = v___x_5315_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_fst_5298_);
v___x_5333_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5337_; 
v___x_5334_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5335_ = l_Lean_JsonNumber_fromNat(v_fst_5305_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set_tag(v___x_5274_, 2);
lean_ctor_set(v___x_5274_, 0, v___x_5335_);
v___x_5337_ = v___x_5274_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5339_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 1, v___x_5337_);
lean_ctor_set(v___x_5308_, 0, v___x_5334_);
v___x_5339_ = v___x_5308_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5334_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v___x_5337_);
v___x_5339_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5343_; 
v___x_5340_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5341_ = l_Lean_JsonNumber_fromNat(v_fst_5312_);
if (v_isShared_5263_ == 0)
{
lean_ctor_set_tag(v___x_5262_, 2);
lean_ctor_set(v___x_5262_, 0, v___x_5341_);
v___x_5343_ = v___x_5262_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5341_);
v___x_5343_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
lean_object* v___x_5345_; 
if (v_isShared_5302_ == 0)
{
lean_ctor_set(v___x_5301_, 1, v___x_5343_);
lean_ctor_set(v___x_5301_, 0, v___x_5340_);
v___x_5345_ = v___x_5301_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5340_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 1, v_fst_5319_);
lean_ctor_set(v___x_5294_, 0, v___x_5346_);
v___x_5348_ = v___x_5294_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_fst_5319_);
v___x_5348_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5352_; 
v___x_5349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_5350_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5350_, 0, v_isUnsafe_5266_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 1, v___x_5350_);
lean_ctor_set(v___x_5287_, 0, v___x_5349_);
v___x_5352_ = v___x_5287_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v___x_5350_);
v___x_5352_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5362_; 
v___x_5353_ = lean_box(0);
v___x_5354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5352_);
lean_ctor_set(v___x_5354_, 1, v___x_5353_);
v___x_5355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5348_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
v___x_5356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5345_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5339_);
lean_ctor_set(v___x_5357_, 1, v___x_5356_);
v___x_5358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5333_);
lean_ctor_set(v___x_5358_, 1, v___x_5357_);
v___x_5359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5330_);
lean_ctor_set(v___x_5359_, 1, v___x_5358_);
v___x_5360_ = l_Lean_Json_mkObj(v___x_5359_);
lean_dec_ref_known(v___x_5359_, 2);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 1, v___x_5360_);
lean_ctor_set(v___x_5278_, 0, v___x_5324_);
v___x_5362_ = v___x_5278_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5324_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v___x_5360_);
v___x_5362_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5362_);
lean_ctor_set(v___x_5363_, 1, v___x_5353_);
v___x_5364_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5363_, v_snd_5320_);
lean_dec_ref_known(v___x_5363_, 2);
return v___x_5364_;
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
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_del_object(v___x_5315_);
lean_dec(v_fst_5312_);
lean_del_object(v___x_5308_);
lean_dec(v_fst_5305_);
lean_del_object(v___x_5301_);
lean_dec(v_fst_5298_);
lean_del_object(v___x_5294_);
lean_dec(v_fst_5291_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_del_object(v___x_5262_);
v_a_5376_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5317_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5317_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_del_object(v___x_5308_);
lean_dec(v_fst_5305_);
lean_del_object(v___x_5301_);
lean_dec(v_fst_5298_);
lean_del_object(v___x_5294_);
lean_dec(v_fst_5291_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_dec(v_all_5267_);
lean_del_object(v___x_5262_);
v_a_5385_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5310_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5310_);
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
lean_del_object(v___x_5301_);
lean_dec(v_fst_5298_);
lean_del_object(v___x_5294_);
lean_dec(v_fst_5291_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_dec(v_all_5267_);
lean_dec_ref(v_value_5265_);
lean_del_object(v___x_5262_);
v_a_5394_ = lean_ctor_get(v___x_5303_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5303_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5303_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5303_);
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
lean_del_object(v___x_5294_);
lean_dec(v_fst_5291_);
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_type_5270_);
lean_dec(v_all_5267_);
lean_dec_ref(v_value_5265_);
lean_del_object(v___x_5262_);
v_a_5403_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5296_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5296_);
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
lean_del_object(v___x_5287_);
lean_del_object(v___x_5283_);
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_type_5270_);
lean_dec(v_levelParams_5269_);
lean_dec(v_all_5267_);
lean_dec_ref(v_value_5265_);
lean_del_object(v___x_5262_);
v_a_5412_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5289_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5289_);
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
}
else
{
lean_del_object(v___x_5278_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_type_5270_);
lean_dec(v_levelParams_5269_);
lean_dec(v_name_5268_);
lean_dec(v_all_5267_);
lean_dec_ref(v_value_5265_);
lean_del_object(v___x_5262_);
return v___x_5280_;
}
}
}
}
else
{
lean_dec_ref(v_type_5270_);
lean_dec(v_levelParams_5269_);
lean_dec(v_name_5268_);
lean_dec(v_all_5267_);
lean_dec_ref(v_value_5265_);
lean_del_object(v___x_5262_);
return v___x_5271_;
}
}
}
case 4:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; 
lean_dec_ref_known(v_val_4803_, 1);
v___x_5427_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5428_ = l_LeanExport_dumpConstant(v___x_5427_, v_a_4692_, v___x_4820_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v_snd_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v_snd_5430_ = lean_ctor_get(v_a_5429_, 1);
lean_inc(v_snd_5430_);
lean_dec(v_a_5429_);
v___x_5431_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5432_ = lean_box(0);
v___x_5433_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5434_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4814_, v___x_5431_, v___x_5433_, v_a_4692_, v_snd_5430_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5461_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5437_ = v___x_5434_;
v_isShared_5438_ = v_isSharedCheck_5461_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5434_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5461_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v_fst_5439_; lean_object* v_fst_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5459_; 
v_fst_5439_ = lean_ctor_get(v_a_5435_, 0);
lean_inc(v_fst_5439_);
v_fst_5440_ = lean_ctor_get(v_fst_5439_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v_fst_5439_);
if (v_isSharedCheck_5459_ == 0)
{
lean_object* v_unused_5460_; 
v_unused_5460_ = lean_ctor_get(v_fst_5439_, 1);
lean_dec(v_unused_5460_);
v___x_5442_ = v_fst_5439_;
v_isShared_5443_ = v_isSharedCheck_5459_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_fst_5440_);
lean_dec(v_fst_5439_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5459_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
if (lean_obj_tag(v_fst_5440_) == 0)
{
lean_object* v_snd_5444_; lean_object* v___x_5446_; 
v_snd_5444_ = lean_ctor_get(v_a_5435_, 1);
lean_inc(v_snd_5444_);
lean_dec(v_a_5435_);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 1, v_snd_5444_);
lean_ctor_set(v___x_5442_, 0, v___x_5432_);
v___x_5446_ = v___x_5442_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5432_);
lean_ctor_set(v_reuseFailAlloc_5450_, 1, v_snd_5444_);
v___x_5446_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
lean_object* v___x_5448_; 
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v___x_5446_);
v___x_5448_ = v___x_5437_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5446_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
else
{
lean_object* v_snd_5451_; lean_object* v_val_5452_; lean_object* v___x_5454_; 
v_snd_5451_ = lean_ctor_get(v_a_5435_, 1);
lean_inc(v_snd_5451_);
lean_dec(v_a_5435_);
v_val_5452_ = lean_ctor_get(v_fst_5440_, 0);
lean_inc(v_val_5452_);
lean_dec_ref_known(v_fst_5440_, 1);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 1, v_snd_5451_);
lean_ctor_set(v___x_5442_, 0, v_val_5452_);
v___x_5454_ = v___x_5442_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_val_5452_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_snd_5451_);
v___x_5454_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5456_; 
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v___x_5454_);
v___x_5456_ = v___x_5437_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5454_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
}
}
else
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
v_a_5462_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5464_ = v___x_5434_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5434_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
}
}
else
{
return v___x_5428_;
}
}
case 5:
{
lean_object* v_val_5470_; lean_object* v_all_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
v_val_5470_ = lean_ctor_get(v_val_4803_, 0);
lean_inc_ref(v_val_5470_);
lean_dec_ref_known(v_val_4803_, 1);
v_all_5471_ = lean_ctor_get(v_val_5470_, 3);
lean_inc(v_all_5471_);
v___x_5472_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5473_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5474_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4814_, v_val_5470_, v_all_5471_, v___x_5473_, v_a_4692_, v___x_4820_);
lean_dec(v_all_5471_);
lean_dec_ref(v_val_5470_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; lean_object* v_fst_5476_; lean_object* v_snd_5477_; lean_object* v_snd_5478_; lean_object* v_fst_5479_; lean_object* v_fst_5480_; lean_object* v_snd_5481_; lean_object* v___x_5482_; size_t v_sz_5483_; size_t v___x_5484_; lean_object* v___x_5485_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_a_5475_);
lean_dec_ref_known(v___x_5474_, 1);
v_fst_5476_ = lean_ctor_get(v_a_5475_, 0);
lean_inc(v_fst_5476_);
v_snd_5477_ = lean_ctor_get(v_fst_5476_, 1);
lean_inc(v_snd_5477_);
v_snd_5478_ = lean_ctor_get(v_a_5475_, 1);
lean_inc(v_snd_5478_);
lean_dec(v_a_5475_);
v_fst_5479_ = lean_ctor_get(v_fst_5476_, 0);
lean_inc(v_fst_5479_);
lean_dec(v_fst_5476_);
v_fst_5480_ = lean_ctor_get(v_snd_5477_, 0);
lean_inc(v_fst_5480_);
v_snd_5481_ = lean_ctor_get(v_snd_5477_, 1);
lean_inc(v_snd_5481_);
lean_dec(v_snd_5477_);
v___x_5482_ = lean_box(0);
v_sz_5483_ = lean_array_size(v_fst_5480_);
v___x_5484_ = ((size_t)0ULL);
v___x_5485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_fst_5480_, v_sz_5483_, v___x_5484_, v___x_5482_, v_a_4692_, v_snd_5478_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v_snd_5487_; lean_object* v___x_5488_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v_snd_5487_ = lean_ctor_get(v_a_5486_, 1);
lean_inc(v_snd_5487_);
lean_dec(v_a_5486_);
v___x_5488_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_4814_, v___x_5472_, v_snd_5481_, v_a_4692_, v_snd_5487_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v_fst_5490_; lean_object* v_snd_5491_; lean_object* v_a_5492_; 
v_a_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc(v_a_5489_);
lean_dec_ref_known(v___x_5488_, 1);
v_fst_5490_ = lean_ctor_get(v_a_5489_, 0);
lean_inc(v_fst_5490_);
v_snd_5491_ = lean_ctor_get(v_a_5489_, 1);
lean_inc(v_snd_5491_);
lean_dec(v_a_5489_);
v_a_5492_ = lean_ctor_get(v_fst_5490_, 0);
lean_inc(v_a_5492_);
lean_dec(v_fst_5490_);
v___y_4700_ = v___x_5482_;
v___y_4701_ = v_fst_5479_;
v___y_4702_ = v_fst_5480_;
v_fst_4703_ = v_a_5492_;
v_snd_4704_ = v_snd_5491_;
goto v___jp_4699_;
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
lean_dec(v_fst_5480_);
lean_dec(v_fst_5479_);
v_a_5493_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5495_ = v___x_5488_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5488_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
else
{
lean_dec(v_snd_5481_);
lean_dec(v_fst_5480_);
lean_dec(v_fst_5479_);
return v___x_5485_;
}
}
else
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5508_; 
v_a_5501_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5503_ = v___x_5474_;
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5474_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5506_; 
if (v_isShared_5504_ == 0)
{
v___x_5506_ = v___x_5503_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
v___x_5506_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
return v___x_5506_;
}
}
}
}
case 6:
{
lean_object* v_val_5509_; lean_object* v_induct_5510_; 
v_val_5509_ = lean_ctor_get(v_val_4803_, 0);
lean_inc_ref(v_val_5509_);
lean_dec_ref_known(v_val_4803_, 1);
v_induct_5510_ = lean_ctor_get(v_val_5509_, 1);
lean_inc(v_induct_5510_);
lean_dec_ref(v_val_5509_);
v_c_4691_ = v_induct_5510_;
v_a_4693_ = v___x_4820_;
goto _start;
}
default: 
{
lean_object* v_val_5512_; lean_object* v_all_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v_val_5512_ = lean_ctor_get(v_val_4803_, 0);
lean_inc_ref(v_val_5512_);
lean_dec_ref_known(v_val_4803_, 1);
v_all_5513_ = lean_ctor_get(v_val_5512_, 1);
lean_inc(v_all_5513_);
lean_dec_ref(v_val_5512_);
v___x_5514_ = lean_box(0);
v___x_5515_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5513_, v___x_5514_, v_a_4692_, v___x_4820_);
lean_dec(v_all_5513_);
if (lean_obj_tag(v___x_5515_) == 0)
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5532_; 
v_a_5516_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5518_ = v___x_5515_;
v_isShared_5519_ = v_isSharedCheck_5532_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5515_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5532_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v_snd_5520_; lean_object* v___x_5522_; uint8_t v_isShared_5523_; uint8_t v_isSharedCheck_5530_; 
v_snd_5520_ = lean_ctor_get(v_a_5516_, 1);
v_isSharedCheck_5530_ = !lean_is_exclusive(v_a_5516_);
if (v_isSharedCheck_5530_ == 0)
{
lean_object* v_unused_5531_; 
v_unused_5531_ = lean_ctor_get(v_a_5516_, 0);
lean_dec(v_unused_5531_);
v___x_5522_ = v_a_5516_;
v_isShared_5523_ = v_isSharedCheck_5530_;
goto v_resetjp_5521_;
}
else
{
lean_inc(v_snd_5520_);
lean_dec(v_a_5516_);
v___x_5522_ = lean_box(0);
v_isShared_5523_ = v_isSharedCheck_5530_;
goto v_resetjp_5521_;
}
v_resetjp_5521_:
{
lean_object* v___x_5525_; 
if (v_isShared_5523_ == 0)
{
lean_ctor_set(v___x_5522_, 0, v___x_5514_);
v___x_5525_ = v___x_5522_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5520_);
v___x_5525_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 0, v___x_5525_);
v___x_5527_ = v___x_5518_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
}
else
{
return v___x_5515_;
}
}
}
}
}
}
else
{
lean_dec(v_val_4803_);
lean_dec(v_c_4691_);
goto v___jp_4695_;
}
}
v___jp_5541_:
{
if (v___y_5542_ == 0)
{
goto v___jp_4804_;
}
else
{
lean_dec(v_val_4803_);
lean_dec(v_c_4691_);
goto v___jp_4695_;
}
}
}
else
{
uint8_t v_ignoreMissing_5545_; 
lean_dec(v___x_4802_);
v_ignoreMissing_5545_ = lean_ctor_get_uint8(v_a_4693_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5545_ == 0)
{
lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; uint8_t v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5546_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_5548_ = lean_unsigned_to_nat(254u);
v___x_5549_ = lean_unsigned_to_nat(48u);
v___x_5550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5551_ = 1;
v___x_5552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4691_, v___x_5551_);
v___x_5553_ = lean_string_append(v___x_5550_, v___x_5552_);
lean_dec_ref(v___x_5552_);
v___x_5554_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5555_ = lean_string_append(v___x_5553_, v___x_5554_);
v___x_5556_ = l_mkPanicMessageWithDecl(v___x_5546_, v___x_5547_, v___x_5548_, v___x_5549_, v___x_5555_);
lean_dec_ref(v___x_5555_);
v___x_5557_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5556_, v_a_4692_, v_a_4693_);
return v___x_5557_;
}
else
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
lean_dec(v_c_4691_);
v___x_5558_ = lean_box(0);
v___x_5559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5558_);
lean_ctor_set(v___x_5559_, 1, v_a_4693_);
v___x_5560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5560_, 0, v___x_5559_);
return v___x_5560_;
}
}
v___jp_4695_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = lean_box(0);
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v_a_4693_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
v___jp_4699_:
{
size_t v_sz_4705_; size_t v___x_4706_; lean_object* v___x_4707_; 
v_sz_4705_ = lean_array_size(v_fst_4703_);
v___x_4706_ = ((size_t)0ULL);
v___x_4707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_4703_, v_sz_4705_, v___x_4706_, v___y_4700_, v_a_4692_, v_snd_4704_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v_snd_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4799_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v_snd_4709_ = lean_ctor_get(v_a_4708_, 1);
v_isSharedCheck_4799_ = !lean_is_exclusive(v_a_4708_);
if (v_isSharedCheck_4799_ == 0)
{
lean_object* v_unused_4800_; 
v_unused_4800_ = lean_ctor_get(v_a_4708_, 0);
lean_dec(v_unused_4800_);
v___x_4711_ = v_a_4708_;
v_isShared_4712_ = v_isSharedCheck_4799_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_snd_4709_);
lean_dec(v_a_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4799_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4713_; 
v___x_4713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_fst_4703_, v_sz_4705_, v___x_4706_, v___y_4700_, v_a_4692_, v_snd_4709_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v_snd_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4797_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc(v_a_4714_);
lean_dec_ref_known(v___x_4713_, 1);
v_snd_4715_ = lean_ctor_get(v_a_4714_, 1);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_a_4714_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v_a_4714_, 0);
lean_dec(v_unused_4798_);
v___x_4717_ = v_a_4714_;
v_isShared_4718_ = v_isSharedCheck_4797_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_snd_4715_);
lean_dec(v_a_4714_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4797_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
size_t v_sz_4719_; lean_object* v___x_4720_; 
v_sz_4719_ = lean_array_size(v___y_4701_);
v___x_4720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_4719_, v___x_4706_, v___y_4701_, v_a_4692_, v_snd_4715_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_fst_4722_; lean_object* v_snd_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4788_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v_fst_4722_ = lean_ctor_get(v_a_4721_, 0);
v_snd_4723_ = lean_ctor_get(v_a_4721_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_a_4721_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4725_ = v_a_4721_;
v_isShared_4726_ = v_isSharedCheck_4788_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_snd_4723_);
lean_inc(v_fst_4722_);
lean_dec(v_a_4721_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4788_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
size_t v_sz_4727_; lean_object* v___x_4728_; 
v_sz_4727_ = lean_array_size(v___y_4702_);
v___x_4728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_4727_, v___x_4706_, v___y_4702_, v_a_4692_, v_snd_4723_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v_fst_4730_; lean_object* v_snd_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4779_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
v_fst_4730_ = lean_ctor_get(v_a_4729_, 0);
v_snd_4731_ = lean_ctor_get(v_a_4729_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_a_4729_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4733_ = v_a_4729_;
v_isShared_4734_ = v_isSharedCheck_4779_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_snd_4731_);
lean_inc(v_fst_4730_);
lean_dec(v_a_4729_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4779_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4705_, v___x_4706_, v_fst_4703_, v_a_4692_, v_snd_4731_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v_fst_4737_; lean_object* v_snd_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4770_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v_fst_4737_ = lean_ctor_get(v_a_4736_, 0);
v_snd_4738_ = lean_ctor_get(v_a_4736_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_a_4736_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4740_ = v_a_4736_;
v_isShared_4741_ = v_isSharedCheck_4770_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_snd_4738_);
lean_inc(v_fst_4737_);
lean_dec(v_a_4736_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4770_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
v___x_4742_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4743_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4744_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4722_);
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 1, v___x_4744_);
lean_ctor_set(v___x_4740_, 0, v___x_4743_);
v___x_4746_ = v___x_4740_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4744_);
v___x_4746_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4750_; 
v___x_4747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_4748_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4730_);
if (v_isShared_4734_ == 0)
{
lean_ctor_set(v___x_4733_, 1, v___x_4748_);
lean_ctor_set(v___x_4733_, 0, v___x_4747_);
v___x_4750_ = v___x_4733_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
v___x_4751_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4752_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4737_);
if (v_isShared_4726_ == 0)
{
lean_ctor_set(v___x_4725_, 1, v___x_4752_);
lean_ctor_set(v___x_4725_, 0, v___x_4751_);
v___x_4754_ = v___x_4725_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4755_ = lean_box(0);
if (v_isShared_4712_ == 0)
{
lean_ctor_set_tag(v___x_4711_, 1);
lean_ctor_set(v___x_4711_, 1, v___x_4755_);
lean_ctor_set(v___x_4711_, 0, v___x_4754_);
v___x_4757_ = v___x_4711_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4754_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v___x_4755_);
v___x_4757_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4750_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4746_);
lean_ctor_set(v___x_4759_, 1, v___x_4758_);
v___x_4760_ = l_Lean_Json_mkObj(v___x_4759_);
lean_dec_ref_known(v___x_4759_, 2);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 1, v___x_4760_);
lean_ctor_set(v___x_4717_, 0, v___x_4742_);
v___x_4762_ = v___x_4717_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
lean_ctor_set(v___x_4763_, 1, v___x_4755_);
v___x_4764_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4763_, v_snd_4738_);
lean_dec_ref_known(v___x_4763_, 2);
return v___x_4764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_del_object(v___x_4733_);
lean_dec(v_fst_4730_);
lean_del_object(v___x_4725_);
lean_dec(v_fst_4722_);
lean_del_object(v___x_4717_);
lean_del_object(v___x_4711_);
v_a_4771_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4735_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4735_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
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
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_del_object(v___x_4725_);
lean_dec(v_fst_4722_);
lean_del_object(v___x_4717_);
lean_del_object(v___x_4711_);
lean_dec_ref(v_fst_4703_);
v_a_4780_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4728_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4728_);
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
lean_del_object(v___x_4717_);
lean_del_object(v___x_4711_);
lean_dec_ref(v_fst_4703_);
lean_dec(v___y_4702_);
v_a_4789_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4720_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4720_);
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
lean_del_object(v___x_4711_);
lean_dec_ref(v_fst_4703_);
lean_dec(v___y_4702_);
lean_dec(v___y_4701_);
return v___x_4713_;
}
}
}
else
{
lean_dec_ref(v_fst_4703_);
lean_dec(v___y_4702_);
lean_dec(v___y_4701_);
return v___x_4707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5561_, size_t v_sz_5562_, size_t v_i_5563_, lean_object* v_b_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
uint8_t v___x_5568_; 
v___x_5568_ = lean_usize_dec_lt(v_i_5563_, v_sz_5562_);
if (v___x_5568_ == 0)
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5569_, 0, v_b_5564_);
lean_ctor_set(v___x_5569_, 1, v___y_5566_);
v___x_5570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5569_);
return v___x_5570_;
}
else
{
lean_object* v___x_5571_; lean_object* v_a_5572_; lean_object* v___x_5573_; 
v___x_5571_ = lean_box(0);
v_a_5572_ = lean_array_uget_borrowed(v_as_5561_, v_i_5563_);
lean_inc(v_a_5572_);
v___x_5573_ = l_LeanExport_dumpConstant(v_a_5572_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v_a_5574_; lean_object* v_snd_5575_; size_t v___x_5576_; size_t v___x_5577_; 
v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
lean_inc(v_a_5574_);
lean_dec_ref_known(v___x_5573_, 1);
v_snd_5575_ = lean_ctor_get(v_a_5574_, 1);
lean_inc(v_snd_5575_);
lean_dec(v_a_5574_);
v___x_5576_ = ((size_t)1ULL);
v___x_5577_ = lean_usize_add(v_i_5563_, v___x_5576_);
v_i_5563_ = v___x_5577_;
v_b_5564_ = v___x_5571_;
v___y_5566_ = v_snd_5575_;
goto _start;
}
else
{
return v___x_5573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; size_t v_sz_5585_; size_t v___x_5586_; lean_object* v___x_5587_; 
v___x_5583_ = l_Lean_Expr_getUsedConstants(v_e_5579_);
v___x_5584_ = lean_box(0);
v_sz_5585_ = lean_array_size(v___x_5583_);
v___x_5586_ = ((size_t)0ULL);
v___x_5587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5583_, v_sz_5585_, v___x_5586_, v___x_5584_, v_a_5580_, v_a_5581_);
lean_dec_ref(v___x_5583_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5604_; 
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5590_ = v___x_5587_;
v_isShared_5591_ = v_isSharedCheck_5604_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5587_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5604_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v_snd_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5602_; 
v_snd_5592_ = lean_ctor_get(v_a_5588_, 1);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_a_5588_);
if (v_isSharedCheck_5602_ == 0)
{
lean_object* v_unused_5603_; 
v_unused_5603_ = lean_ctor_get(v_a_5588_, 0);
lean_dec(v_unused_5603_);
v___x_5594_ = v_a_5588_;
v_isShared_5595_ = v_isSharedCheck_5602_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_snd_5592_);
lean_dec(v_a_5588_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5602_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 0, v___x_5584_);
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5584_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v_snd_5592_);
v___x_5597_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
lean_object* v___x_5599_; 
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 0, v___x_5597_);
v___x_5599_ = v___x_5590_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5597_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
}
else
{
return v___x_5587_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5605_, v_a_5606_, v_a_5607_);
lean_dec_ref(v_a_5606_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5610_, lean_object* v_b_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5610_, v_b_5611_, v___y_5612_, v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v_as_x27_5610_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5616_, lean_object* v_b_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5616_, v_b_5617_, v___y_5618_, v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v_as_x27_5616_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5622_, lean_object* v_x_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_){
_start:
{
lean_object* v_res_5627_; 
v_res_5627_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5622_, v_x_5623_, v___y_5624_, v___y_5625_);
lean_dec_ref(v___y_5624_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5628_, lean_object* v_sz_5629_, lean_object* v_i_5630_, lean_object* v_b_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_){
_start:
{
size_t v_sz_boxed_5635_; size_t v_i_boxed_5636_; lean_object* v_res_5637_; 
v_sz_boxed_5635_ = lean_unbox_usize(v_sz_5629_);
lean_dec(v_sz_5629_);
v_i_boxed_5636_ = lean_unbox_usize(v_i_5630_);
lean_dec(v_i_5630_);
v_res_5637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5628_, v_sz_boxed_5635_, v_i_boxed_5636_, v_b_5631_, v___y_5632_, v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec_ref(v_as_5628_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_){
_start:
{
lean_object* v_res_5641_; 
v_res_5641_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5638_, v_a_5639_);
lean_dec_ref(v_a_5638_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v_as_5642_, lean_object* v_sz_5643_, lean_object* v_i_5644_, lean_object* v_b_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_){
_start:
{
size_t v_sz_boxed_5649_; size_t v_i_boxed_5650_; lean_object* v_res_5651_; 
v_sz_boxed_5649_ = lean_unbox_usize(v_sz_5643_);
lean_dec(v_sz_5643_);
v_i_boxed_5650_ = lean_unbox_usize(v_i_5644_);
lean_dec(v_i_5644_);
v_res_5651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_as_5642_, v_sz_boxed_5649_, v_i_boxed_5650_, v_b_5645_, v___y_5646_, v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec_ref(v_as_5642_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l_LeanExport_dumpExpr(v_e_5652_, v_a_5653_, v_a_5654_);
lean_dec_ref(v_a_5653_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5657_, lean_object* v_sz_5658_, lean_object* v_i_5659_, lean_object* v_b_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
size_t v_sz_boxed_5664_; size_t v_i_boxed_5665_; lean_object* v_res_5666_; 
v_sz_boxed_5664_ = lean_unbox_usize(v_sz_5658_);
lean_dec(v_sz_5658_);
v_i_boxed_5665_ = lean_unbox_usize(v_i_5659_);
lean_dec(v_i_5659_);
v_res_5666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5657_, v_sz_boxed_5664_, v_i_boxed_5665_, v_b_5660_, v___y_5661_, v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec_ref(v_as_5657_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_as_5667_, lean_object* v_sz_5668_, lean_object* v_i_5669_, lean_object* v_b_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
size_t v_sz_boxed_5674_; size_t v_i_boxed_5675_; lean_object* v_res_5676_; 
v_sz_boxed_5674_ = lean_unbox_usize(v_sz_5668_);
lean_dec(v_sz_5668_);
v_i_boxed_5675_ = lean_unbox_usize(v_i_5669_);
lean_dec(v_i_5669_);
v_res_5676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_as_5667_, v_sz_boxed_5674_, v_i_boxed_5675_, v_b_5670_, v___y_5671_, v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec_ref(v_as_5667_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v_res_5681_; 
v_res_5681_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5677_, v_a_5678_, v_a_5679_);
lean_dec_ref(v_a_5678_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5682_, v_a_5683_);
lean_dec_ref(v_a_5682_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_sz_5686_, lean_object* v_i_5687_, lean_object* v_bs_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
size_t v_sz_boxed_5692_; size_t v_i_boxed_5693_; lean_object* v_res_5694_; 
v_sz_boxed_5692_ = lean_unbox_usize(v_sz_5686_);
lean_dec(v_sz_5686_);
v_i_boxed_5693_ = lean_unbox_usize(v_i_5687_);
lean_dec(v_i_5687_);
v_res_5694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_boxed_5692_, v_i_boxed_5693_, v_bs_5688_, v___y_5689_, v___y_5690_);
lean_dec_ref(v___y_5689_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5695_, lean_object* v_as_x27_5696_, lean_object* v_b_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
uint8_t v___x_173066__boxed_5701_; lean_object* v_res_5702_; 
v___x_173066__boxed_5701_ = lean_unbox(v___x_5695_);
v_res_5702_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173066__boxed_5701_, v_as_x27_5696_, v_b_5697_, v___y_5698_, v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v_as_x27_5696_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_sz_5703_, lean_object* v_i_5704_, lean_object* v_bs_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
size_t v_sz_boxed_5709_; size_t v_i_boxed_5710_; lean_object* v_res_5711_; 
v_sz_boxed_5709_ = lean_unbox_usize(v_sz_5703_);
lean_dec(v_sz_5703_);
v_i_boxed_5710_ = lean_unbox_usize(v_i_5704_);
lean_dec(v_i_5704_);
v_res_5711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_boxed_5709_, v_i_boxed_5710_, v_bs_5705_, v___y_5706_, v___y_5707_);
lean_dec_ref(v___y_5706_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5721_, lean_object* v_val_5722_, lean_object* v_as_x27_5723_, lean_object* v_b_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_){
_start:
{
uint8_t v___x_173371__boxed_5728_; lean_object* v_res_5729_; 
v___x_173371__boxed_5728_ = lean_unbox(v___x_5721_);
v_res_5729_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173371__boxed_5728_, v_val_5722_, v_as_x27_5723_, v_b_5724_, v___y_5725_, v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v_as_x27_5723_);
lean_dec_ref(v_val_5722_);
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_LeanExport_dumpExprAux(v_e_5730_, v_a_5731_, v_a_5732_);
lean_dec_ref(v_a_5731_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l_LeanExport_dumpConstant(v_c_5735_, v_a_5736_, v_a_5737_);
lean_dec_ref(v_a_5736_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5740_, lean_object* v_as_5741_, lean_object* v_as_x27_5742_, lean_object* v_b_5743_, lean_object* v_a_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_){
_start:
{
lean_object* v___x_5748_; 
v___x_5748_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5740_, v_as_x27_5742_, v_b_5743_, v___y_5745_, v___y_5746_);
return v___x_5748_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5749_, lean_object* v_as_5750_, lean_object* v_as_x27_5751_, lean_object* v_b_5752_, lean_object* v_a_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_){
_start:
{
uint8_t v___x_177936__boxed_5757_; lean_object* v_res_5758_; 
v___x_177936__boxed_5757_ = lean_unbox(v___x_5749_);
v_res_5758_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_177936__boxed_5757_, v_as_5750_, v_as_x27_5751_, v_b_5752_, v_a_5753_, v___y_5754_, v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v_as_x27_5751_);
lean_dec(v_as_5750_);
return v_res_5758_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5759_, uint8_t v___x_5760_, lean_object* v_as_5761_, lean_object* v_as_x27_5762_, lean_object* v_b_5763_, lean_object* v_a_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
lean_object* v___x_5768_; 
v___x_5768_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5759_, v___x_5760_, v_as_x27_5762_, v_b_5763_, v___y_5765_, v___y_5766_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5769_, lean_object* v___x_5770_, lean_object* v_as_5771_, lean_object* v_as_x27_5772_, lean_object* v_b_5773_, lean_object* v_a_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
uint8_t v___y_177953__boxed_5778_; uint8_t v___x_177954__boxed_5779_; lean_object* v_res_5780_; 
v___y_177953__boxed_5778_ = lean_unbox(v___y_5769_);
v___x_177954__boxed_5779_ = lean_unbox(v___x_5770_);
v_res_5780_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_177953__boxed_5778_, v___x_177954__boxed_5779_, v_as_5771_, v_as_x27_5772_, v_b_5773_, v_a_5774_, v___y_5775_, v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v_as_x27_5772_);
lean_dec(v_as_5771_);
return v_res_5780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5781_, lean_object* v_t_5782_, lean_object* v_k_5783_){
_start:
{
lean_object* v___x_5784_; 
v___x_5784_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5782_, v_k_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_5785_, lean_object* v_t_5786_, lean_object* v_k_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_5785_, v_t_5786_, v_k_5787_);
lean_dec(v_k_5787_);
lean_dec(v_t_5786_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_5789_, lean_object* v_val_5790_, lean_object* v_as_5791_, lean_object* v_as_x27_5792_, lean_object* v_b_5793_, lean_object* v_a_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5789_, v_val_5790_, v_as_x27_5792_, v_b_5793_, v___y_5795_, v___y_5796_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_5799_, lean_object* v_val_5800_, lean_object* v_as_5801_, lean_object* v_as_x27_5802_, lean_object* v_b_5803_, lean_object* v_a_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_){
_start:
{
uint8_t v___x_177975__boxed_5808_; lean_object* v_res_5809_; 
v___x_177975__boxed_5808_ = lean_unbox(v___x_5799_);
v_res_5809_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_177975__boxed_5808_, v_val_5800_, v_as_5801_, v_as_x27_5802_, v_b_5803_, v_a_5804_, v___y_5805_, v___y_5806_);
lean_dec_ref(v___y_5805_);
lean_dec(v_as_x27_5802_);
lean_dec(v_as_5801_);
lean_dec_ref(v_val_5800_);
return v_res_5809_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_5810_, lean_object* v_as_x27_5811_, lean_object* v_b_5812_, lean_object* v_a_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
lean_object* v___x_5817_; 
v___x_5817_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5811_, v_b_5812_, v___y_5814_, v___y_5815_);
return v___x_5817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_5818_, lean_object* v_as_x27_5819_, lean_object* v_b_5820_, lean_object* v_a_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5818_, v_as_x27_5819_, v_b_5820_, v_a_5821_, v___y_5822_, v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v_as_x27_5819_);
lean_dec(v_as_5818_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_5826_, lean_object* v_as_x27_5827_, lean_object* v_b_5828_, lean_object* v_a_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_){
_start:
{
lean_object* v___x_5833_; 
v___x_5833_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5827_, v_b_5828_, v___y_5830_, v___y_5831_);
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_5834_, lean_object* v_as_x27_5835_, lean_object* v_b_5836_, lean_object* v_a_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_){
_start:
{
lean_object* v_res_5841_; 
v_res_5841_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5834_, v_as_x27_5835_, v_b_5836_, v_a_5837_, v___y_5838_, v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v_as_x27_5835_);
lean_dec(v_as_5834_);
return v_res_5841_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = l_Lean_versionString;
v___x_5844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5844_, 0, v___x_5843_);
return v___x_5844_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5845_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_5846_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5847_, 0, v___x_5846_);
lean_ctor_set(v___x_5847_, 1, v___x_5845_);
return v___x_5847_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = l_Lean_githash;
v___x_5850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5850_, 0, v___x_5849_);
return v___x_5850_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5851_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_5852_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_5853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5852_);
lean_ctor_set(v___x_5853_, 1, v___x_5851_);
return v___x_5853_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5854_ = lean_box(0);
v___x_5855_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_5856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
lean_ctor_set(v___x_5856_, 1, v___x_5854_);
return v___x_5856_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_5858_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_5859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
lean_ctor_set(v___x_5859_, 1, v___x_5857_);
return v___x_5859_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_5860_; lean_object* v_leanMeta_5861_; 
v___x_5860_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_5861_ = l_Lean_Json_mkObj(v___x_5860_);
return v_leanMeta_5861_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_5880_; lean_object* v_exporterMeta_5881_; 
v___x_5880_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_5881_ = l_Lean_Json_mkObj(v___x_5880_);
return v_exporterMeta_5881_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_5882_; lean_object* v_formatMeta_5883_; 
v___x_5882_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_5883_ = l_Lean_Json_mkObj(v___x_5882_);
return v_formatMeta_5883_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v_exporterMeta_5886_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_5887_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_5888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5887_);
lean_ctor_set(v___x_5888_, 1, v_exporterMeta_5886_);
return v___x_5888_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v_leanMeta_5890_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_5891_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_5892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5891_);
lean_ctor_set(v___x_5892_, 1, v_leanMeta_5890_);
return v___x_5892_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; 
v_formatMeta_5894_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_5895_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_5896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5895_);
lean_ctor_set(v___x_5896_, 1, v_formatMeta_5894_);
return v___x_5896_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5897_ = lean_box(0);
v___x_5898_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_5899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v___x_5897_);
return v___x_5899_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5900_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_5901_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_5902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5901_);
lean_ctor_set(v___x_5902_, 1, v___x_5900_);
return v___x_5902_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v___x_5903_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_5904_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_5905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
lean_ctor_set(v___x_5905_, 1, v___x_5903_);
return v___x_5905_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5906_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_5907_ = l_Lean_Json_mkObj(v___x_5906_);
return v___x_5907_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5908_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_5909_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_5910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
lean_ctor_set(v___x_5910_, 1, v___x_5908_);
return v___x_5910_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5911_ = lean_box(0);
v___x_5912_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_5913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5912_);
lean_ctor_set(v___x_5913_, 1, v___x_5911_);
return v___x_5913_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; 
v___x_5914_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_5915_ = l_Lean_Json_mkObj(v___x_5914_);
return v___x_5915_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_5916_; 
v___x_5916_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_5916_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; 
v___x_5917_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_5918_ = l_Lean_Json_compress(v___x_5917_);
return v___x_5918_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_5919_){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_5922_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_5921_);
if (lean_obj_tag(v___x_5922_) == 0)
{
lean_object* v_a_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5931_; 
v_a_5923_ = lean_ctor_get(v___x_5922_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5922_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5925_ = v___x_5922_;
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v___x_5922_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v___x_5927_; lean_object* v___x_5929_; 
v___x_5927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5927_, 0, v_a_5923_);
lean_ctor_set(v___x_5927_, 1, v_a_5919_);
if (v_isShared_5926_ == 0)
{
lean_ctor_set(v___x_5925_, 0, v___x_5927_);
v___x_5929_ = v___x_5925_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v___x_5927_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5939_; 
lean_dec_ref(v_a_5919_);
v_a_5932_ = lean_ctor_get(v___x_5922_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5922_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5934_ = v___x_5922_;
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5922_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5937_; 
if (v_isShared_5935_ == 0)
{
v___x_5937_ = v___x_5934_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
return v___x_5937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v_res_5942_; 
v_res_5942_ = l_LeanExport_dumpMetadata___redArg(v_a_5940_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_5943_, lean_object* v_a_5944_){
_start:
{
lean_object* v___x_5946_; 
v___x_5946_ = l_LeanExport_dumpMetadata___redArg(v_a_5944_);
return v___x_5946_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_LeanExport_dumpMetadata(v_a_5947_, v_a_5948_);
lean_dec_ref(v_a_5947_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object* v_as_x27_5951_, lean_object* v_b_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
if (lean_obj_tag(v_as_x27_5951_) == 0)
{
lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5956_, 0, v_b_5952_);
lean_ctor_set(v___x_5956_, 1, v___y_5954_);
v___x_5957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
return v___x_5957_;
}
else
{
lean_object* v_head_5958_; lean_object* v_tail_5959_; lean_object* v_visitedNames_5960_; lean_object* v_visitedLevels_5961_; lean_object* v_visitedExprs_5962_; lean_object* v_visitedConstants_5963_; uint8_t v_exportMData_5964_; uint8_t v_exportUnsafe_5965_; uint8_t v_ignoreMissing_5966_; lean_object* v_recursorMap_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5980_; 
v_head_5958_ = lean_ctor_get(v_as_x27_5951_, 0);
v_tail_5959_ = lean_ctor_get(v_as_x27_5951_, 1);
v_visitedNames_5960_ = lean_ctor_get(v___y_5954_, 0);
v_visitedLevels_5961_ = lean_ctor_get(v___y_5954_, 1);
v_visitedExprs_5962_ = lean_ctor_get(v___y_5954_, 2);
v_visitedConstants_5963_ = lean_ctor_get(v___y_5954_, 3);
v_exportMData_5964_ = lean_ctor_get_uint8(v___y_5954_, sizeof(void*)*6);
v_exportUnsafe_5965_ = lean_ctor_get_uint8(v___y_5954_, sizeof(void*)*6 + 1);
v_ignoreMissing_5966_ = lean_ctor_get_uint8(v___y_5954_, sizeof(void*)*6 + 2);
v_recursorMap_5967_ = lean_ctor_get(v___y_5954_, 5);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___y_5954_);
if (v_isSharedCheck_5980_ == 0)
{
lean_object* v_unused_5981_; 
v_unused_5981_ = lean_ctor_get(v___y_5954_, 4);
lean_dec(v_unused_5981_);
v___x_5969_ = v___y_5954_;
v_isShared_5970_ = v_isSharedCheck_5980_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_recursorMap_5967_);
lean_inc(v_visitedConstants_5963_);
lean_inc(v_visitedExprs_5962_);
lean_inc(v_visitedLevels_5961_);
lean_inc(v_visitedNames_5960_);
lean_dec(v___y_5954_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5980_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5971_ = lean_box(0);
v___x_5972_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 4, v___x_5972_);
v___x_5974_ = v___x_5969_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_visitedNames_5960_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_visitedLevels_5961_);
lean_ctor_set(v_reuseFailAlloc_5979_, 2, v_visitedExprs_5962_);
lean_ctor_set(v_reuseFailAlloc_5979_, 3, v_visitedConstants_5963_);
lean_ctor_set(v_reuseFailAlloc_5979_, 4, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5979_, 5, v_recursorMap_5967_);
lean_ctor_set_uint8(v_reuseFailAlloc_5979_, sizeof(void*)*6, v_exportMData_5964_);
lean_ctor_set_uint8(v_reuseFailAlloc_5979_, sizeof(void*)*6 + 1, v_exportUnsafe_5965_);
lean_ctor_set_uint8(v_reuseFailAlloc_5979_, sizeof(void*)*6 + 2, v_ignoreMissing_5966_);
v___x_5974_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; 
lean_inc(v_head_5958_);
v___x_5975_ = l_LeanExport_dumpConstant(v_head_5958_, v___y_5953_, v___x_5974_);
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v_a_5976_; lean_object* v_snd_5977_; 
v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
lean_inc(v_a_5976_);
lean_dec_ref_known(v___x_5975_, 1);
v_snd_5977_ = lean_ctor_get(v_a_5976_, 1);
lean_inc(v_snd_5977_);
lean_dec(v_a_5976_);
v_as_x27_5951_ = v_tail_5959_;
v_b_5952_ = v___x_5971_;
v___y_5954_ = v_snd_5977_;
goto _start;
}
else
{
return v___x_5975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object* v_as_x27_5982_, lean_object* v_b_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
lean_object* v_res_5987_; 
v_res_5987_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_5982_, v_b_5983_, v___y_5984_, v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v_as_x27_5982_);
return v_res_5987_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object* v_env_5988_, lean_object* v_cliOptions_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = l_LeanExport_initState(v_env_5988_, v_cliOptions_5989_, v___y_5991_, v___y_5992_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; lean_object* v_snd_5996_; lean_object* v___x_5997_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
lean_inc(v_a_5995_);
lean_dec_ref_known(v___x_5994_, 1);
v_snd_5996_ = lean_ctor_get(v_a_5995_, 1);
lean_inc(v_snd_5996_);
lean_dec(v_a_5995_);
v___x_5997_ = l_LeanExport_dumpMetadata___redArg(v_snd_5996_);
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_object* v_a_5998_; lean_object* v_snd_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v_a_5998_ = lean_ctor_get(v___x_5997_, 0);
lean_inc(v_a_5998_);
lean_dec_ref_known(v___x_5997_, 1);
v_snd_5999_ = lean_ctor_get(v_a_5998_, 1);
lean_inc(v_snd_5999_);
lean_dec(v_a_5998_);
v___x_6000_ = lean_box(0);
v___x_6001_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v___y_5990_, v___x_6000_, v___y_5991_, v_snd_5999_);
if (lean_obj_tag(v___x_6001_) == 0)
{
lean_object* v_a_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6018_; 
v_a_6002_ = lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6018_ = !lean_is_exclusive(v___x_6001_);
if (v_isSharedCheck_6018_ == 0)
{
v___x_6004_ = v___x_6001_;
v_isShared_6005_ = v_isSharedCheck_6018_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_a_6002_);
lean_dec(v___x_6001_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6018_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
lean_object* v_snd_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6016_; 
v_snd_6006_ = lean_ctor_get(v_a_6002_, 1);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_a_6002_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; 
v_unused_6017_ = lean_ctor_get(v_a_6002_, 0);
lean_dec(v_unused_6017_);
v___x_6008_ = v_a_6002_;
v_isShared_6009_ = v_isSharedCheck_6016_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_snd_6006_);
lean_dec(v_a_6002_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6016_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
if (v_isShared_6009_ == 0)
{
lean_ctor_set(v___x_6008_, 0, v___x_6000_);
v___x_6011_ = v___x_6008_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v___x_6000_);
lean_ctor_set(v_reuseFailAlloc_6015_, 1, v_snd_6006_);
v___x_6011_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
lean_object* v___x_6013_; 
if (v_isShared_6005_ == 0)
{
lean_ctor_set(v___x_6004_, 0, v___x_6011_);
v___x_6013_ = v___x_6004_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v___x_6011_);
v___x_6013_ = v_reuseFailAlloc_6014_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
return v___x_6013_;
}
}
}
}
}
else
{
return v___x_6001_;
}
}
else
{
return v___x_5997_;
}
}
else
{
return v___x_5994_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object* v_env_6019_, lean_object* v_cliOptions_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_LeanExport_dumpEnv___lam__0(v_env_6019_, v_cliOptions_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
lean_dec_ref(v___y_6022_);
lean_dec(v___y_6021_);
lean_dec(v_cliOptions_6020_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object* v_es_6026_, lean_object* v_a_6027_, lean_object* v_b_6028_){
_start:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6029_, 0, v_a_6027_);
lean_ctor_set(v___x_6029_, 1, v_b_6028_);
v___x_6030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6029_);
lean_ctor_set(v___x_6030_, 1, v_es_6026_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object* v_f_6031_, lean_object* v_x_6032_, lean_object* v_x_6033_){
_start:
{
if (lean_obj_tag(v_x_6033_) == 0)
{
lean_dec(v_f_6031_);
return v_x_6032_;
}
else
{
lean_object* v_key_6034_; lean_object* v_value_6035_; lean_object* v_tail_6036_; lean_object* v___x_6037_; 
v_key_6034_ = lean_ctor_get(v_x_6033_, 0);
lean_inc(v_key_6034_);
v_value_6035_ = lean_ctor_get(v_x_6033_, 1);
lean_inc(v_value_6035_);
v_tail_6036_ = lean_ctor_get(v_x_6033_, 2);
lean_inc(v_tail_6036_);
lean_dec_ref_known(v_x_6033_, 3);
lean_inc(v_f_6031_);
v___x_6037_ = lean_apply_3(v_f_6031_, v_x_6032_, v_key_6034_, v_value_6035_);
v_x_6032_ = v___x_6037_;
v_x_6033_ = v_tail_6036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object* v_f_6039_, lean_object* v_as_6040_, size_t v_i_6041_, size_t v_stop_6042_, lean_object* v_b_6043_){
_start:
{
uint8_t v___x_6044_; 
v___x_6044_ = lean_usize_dec_eq(v_i_6041_, v_stop_6042_);
if (v___x_6044_ == 0)
{
lean_object* v___x_6045_; lean_object* v___x_6046_; size_t v___x_6047_; size_t v___x_6048_; 
v___x_6045_ = lean_array_uget_borrowed(v_as_6040_, v_i_6041_);
lean_inc(v___x_6045_);
lean_inc(v_f_6039_);
v___x_6046_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6039_, v_b_6043_, v___x_6045_);
v___x_6047_ = ((size_t)1ULL);
v___x_6048_ = lean_usize_add(v_i_6041_, v___x_6047_);
v_i_6041_ = v___x_6048_;
v_b_6043_ = v___x_6046_;
goto _start;
}
else
{
lean_dec(v_f_6039_);
return v_b_6043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_f_6050_, lean_object* v_as_6051_, lean_object* v_i_6052_, lean_object* v_stop_6053_, lean_object* v_b_6054_){
_start:
{
size_t v_i_boxed_6055_; size_t v_stop_boxed_6056_; lean_object* v_res_6057_; 
v_i_boxed_6055_ = lean_unbox_usize(v_i_6052_);
lean_dec(v_i_6052_);
v_stop_boxed_6056_ = lean_unbox_usize(v_stop_6053_);
lean_dec(v_stop_6053_);
v_res_6057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6050_, v_as_6051_, v_i_boxed_6055_, v_stop_boxed_6056_, v_b_6054_);
lean_dec_ref(v_as_6051_);
return v_res_6057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_f_6058_, lean_object* v_x1_6059_, lean_object* v_x2_6060_, lean_object* v_x3_6061_){
_start:
{
lean_object* v___x_6062_; 
v___x_6062_ = lean_apply_3(v_f_6058_, v_x1_6059_, v_x2_6060_, v_x3_6061_);
return v___x_6062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object* v_f_6063_, lean_object* v_keys_6064_, lean_object* v_vals_6065_, lean_object* v_i_6066_, lean_object* v_acc_6067_){
_start:
{
lean_object* v___x_6068_; uint8_t v___x_6069_; 
v___x_6068_ = lean_array_get_size(v_keys_6064_);
v___x_6069_ = lean_nat_dec_lt(v_i_6066_, v___x_6068_);
if (v___x_6069_ == 0)
{
lean_dec(v_i_6066_);
lean_dec(v_f_6063_);
return v_acc_6067_;
}
else
{
lean_object* v_k_6070_; lean_object* v_v_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v_k_6070_ = lean_array_fget_borrowed(v_keys_6064_, v_i_6066_);
v_v_6071_ = lean_array_fget_borrowed(v_vals_6065_, v_i_6066_);
lean_inc(v_f_6063_);
lean_inc(v_v_6071_);
lean_inc(v_k_6070_);
v___x_6072_ = lean_apply_3(v_f_6063_, v_acc_6067_, v_k_6070_, v_v_6071_);
v___x_6073_ = lean_unsigned_to_nat(1u);
v___x_6074_ = lean_nat_add(v_i_6066_, v___x_6073_);
lean_dec(v_i_6066_);
v_i_6066_ = v___x_6074_;
v_acc_6067_ = v___x_6072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_f_6076_, lean_object* v_keys_6077_, lean_object* v_vals_6078_, lean_object* v_i_6079_, lean_object* v_acc_6080_){
_start:
{
lean_object* v_res_6081_; 
v_res_6081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6076_, v_keys_6077_, v_vals_6078_, v_i_6079_, v_acc_6080_);
lean_dec_ref(v_vals_6078_);
lean_dec_ref(v_keys_6077_);
return v_res_6081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object* v_f_6082_, lean_object* v_as_6083_, size_t v_i_6084_, size_t v_stop_6085_, lean_object* v_b_6086_){
_start:
{
lean_object* v___y_6088_; uint8_t v___x_6092_; 
v___x_6092_ = lean_usize_dec_eq(v_i_6084_, v_stop_6085_);
if (v___x_6092_ == 0)
{
lean_object* v___x_6093_; 
v___x_6093_ = lean_array_uget_borrowed(v_as_6083_, v_i_6084_);
switch(lean_obj_tag(v___x_6093_))
{
case 0:
{
lean_object* v_key_6094_; lean_object* v_val_6095_; lean_object* v___x_6096_; 
v_key_6094_ = lean_ctor_get(v___x_6093_, 0);
v_val_6095_ = lean_ctor_get(v___x_6093_, 1);
lean_inc(v_f_6082_);
lean_inc(v_val_6095_);
lean_inc(v_key_6094_);
v___x_6096_ = lean_apply_3(v_f_6082_, v_b_6086_, v_key_6094_, v_val_6095_);
v___y_6088_ = v___x_6096_;
goto v___jp_6087_;
}
case 1:
{
lean_object* v_node_6097_; lean_object* v___x_6098_; 
v_node_6097_ = lean_ctor_get(v___x_6093_, 0);
lean_inc(v_f_6082_);
v___x_6098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6082_, v_node_6097_, v_b_6086_);
v___y_6088_ = v___x_6098_;
goto v___jp_6087_;
}
default: 
{
v___y_6088_ = v_b_6086_;
goto v___jp_6087_;
}
}
}
else
{
lean_dec(v_f_6082_);
return v_b_6086_;
}
v___jp_6087_:
{
size_t v___x_6089_; size_t v___x_6090_; 
v___x_6089_ = ((size_t)1ULL);
v___x_6090_ = lean_usize_add(v_i_6084_, v___x_6089_);
v_i_6084_ = v___x_6090_;
v_b_6086_ = v___y_6088_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_f_6099_, lean_object* v_x_6100_, lean_object* v_x_6101_){
_start:
{
if (lean_obj_tag(v_x_6100_) == 0)
{
lean_object* v_es_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; uint8_t v___x_6105_; 
v_es_6102_ = lean_ctor_get(v_x_6100_, 0);
v___x_6103_ = lean_unsigned_to_nat(0u);
v___x_6104_ = lean_array_get_size(v_es_6102_);
v___x_6105_ = lean_nat_dec_lt(v___x_6103_, v___x_6104_);
if (v___x_6105_ == 0)
{
lean_dec(v_f_6099_);
return v_x_6101_;
}
else
{
size_t v___x_6106_; size_t v___x_6107_; lean_object* v___x_6108_; 
v___x_6106_ = ((size_t)0ULL);
v___x_6107_ = lean_usize_of_nat(v___x_6104_);
v___x_6108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6099_, v_es_6102_, v___x_6106_, v___x_6107_, v_x_6101_);
return v___x_6108_;
}
}
else
{
lean_object* v_ks_6109_; lean_object* v_vs_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v_ks_6109_ = lean_ctor_get(v_x_6100_, 0);
v_vs_6110_ = lean_ctor_get(v_x_6100_, 1);
v___x_6111_ = lean_unsigned_to_nat(0u);
v___x_6112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6099_, v_ks_6109_, v_vs_6110_, v___x_6111_, v_x_6101_);
return v___x_6112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_6113_, lean_object* v_x_6114_, lean_object* v_x_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6113_, v_x_6114_, v_x_6115_);
lean_dec_ref(v_x_6114_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_f_6117_, lean_object* v_as_6118_, lean_object* v_i_6119_, lean_object* v_stop_6120_, lean_object* v_b_6121_){
_start:
{
size_t v_i_boxed_6122_; size_t v_stop_boxed_6123_; lean_object* v_res_6124_; 
v_i_boxed_6122_ = lean_unbox_usize(v_i_6119_);
lean_dec(v_i_6119_);
v_stop_boxed_6123_ = lean_unbox_usize(v_stop_6120_);
lean_dec(v_stop_6120_);
v_res_6124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6117_, v_as_6118_, v_i_boxed_6122_, v_stop_boxed_6123_, v_b_6121_);
lean_dec_ref(v_as_6118_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object* v_map_6125_, lean_object* v_f_6126_, lean_object* v_init_6127_){
_start:
{
lean_object* v___f_6128_; lean_object* v___x_6129_; 
v___f_6128_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_6128_, 0, v_f_6126_);
v___x_6129_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v___f_6128_, v_map_6125_, v_init_6127_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_map_6130_, lean_object* v_f_6131_, lean_object* v_init_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6130_, v_f_6131_, v_init_6132_);
lean_dec_ref(v_map_6130_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object* v_f_6134_, lean_object* v_init_6135_, lean_object* v_m_6136_){
_start:
{
lean_object* v_map_u2081_6137_; lean_object* v_map_u2082_6138_; lean_object* v_buckets_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; uint8_t v___x_6142_; 
v_map_u2081_6137_ = lean_ctor_get(v_m_6136_, 0);
v_map_u2082_6138_ = lean_ctor_get(v_m_6136_, 1);
v_buckets_6139_ = lean_ctor_get(v_map_u2081_6137_, 1);
v___x_6140_ = lean_unsigned_to_nat(0u);
v___x_6141_ = lean_array_get_size(v_buckets_6139_);
v___x_6142_ = lean_nat_dec_lt(v___x_6140_, v___x_6141_);
if (v___x_6142_ == 0)
{
lean_object* v___x_6143_; 
v___x_6143_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6138_, v_f_6134_, v_init_6135_);
return v___x_6143_;
}
else
{
size_t v___x_6144_; size_t v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; 
v___x_6144_ = ((size_t)0ULL);
v___x_6145_ = lean_usize_of_nat(v___x_6141_);
lean_inc(v_f_6134_);
v___x_6146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6134_, v_buckets_6139_, v___x_6144_, v___x_6145_, v_init_6135_);
v___x_6147_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6138_, v_f_6134_, v___x_6146_);
return v___x_6147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_6148_, lean_object* v_init_6149_, lean_object* v_m_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6148_, v_init_6149_, v_m_6150_);
lean_dec_ref(v_m_6150_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object* v_m_6153_){
_start:
{
lean_object* v___f_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___f_6154_ = ((lean_object*)(l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0));
v___x_6155_ = lean_box(0);
v___x_6156_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v___f_6154_, v___x_6155_, v_m_6153_);
return v___x_6156_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object* v_m_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6157_);
lean_dec_ref(v_m_6157_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object* v_a_6159_, lean_object* v_a_6160_){
_start:
{
if (lean_obj_tag(v_a_6159_) == 0)
{
lean_object* v___x_6161_; 
v___x_6161_ = l_List_reverse___redArg(v_a_6160_);
return v___x_6161_;
}
else
{
lean_object* v_head_6162_; lean_object* v_tail_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6173_; 
v_head_6162_ = lean_ctor_get(v_a_6159_, 0);
v_tail_6163_ = lean_ctor_get(v_a_6159_, 1);
v_isSharedCheck_6173_ = !lean_is_exclusive(v_a_6159_);
if (v_isSharedCheck_6173_ == 0)
{
v___x_6165_ = v_a_6159_;
v_isShared_6166_ = v_isSharedCheck_6173_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_tail_6163_);
lean_inc(v_head_6162_);
lean_dec(v_a_6159_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6173_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
uint8_t v___x_6167_; 
v___x_6167_ = l_Lean_Name_isInternal(v_head_6162_);
if (v___x_6167_ == 0)
{
lean_object* v___x_6169_; 
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 1, v_a_6160_);
v___x_6169_ = v___x_6165_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_head_6162_);
lean_ctor_set(v_reuseFailAlloc_6171_, 1, v_a_6160_);
v___x_6169_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
v_a_6159_ = v_tail_6163_;
v_a_6160_ = v___x_6169_;
goto _start;
}
}
else
{
lean_del_object(v___x_6165_);
lean_dec(v_head_6162_);
v_a_6159_ = v_tail_6163_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object* v_a_6174_, lean_object* v_a_6175_){
_start:
{
if (lean_obj_tag(v_a_6174_) == 0)
{
lean_object* v___x_6176_; 
v___x_6176_ = l_List_reverse___redArg(v_a_6175_);
return v___x_6176_;
}
else
{
lean_object* v_head_6177_; lean_object* v_tail_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6187_; 
v_head_6177_ = lean_ctor_get(v_a_6174_, 0);
v_tail_6178_ = lean_ctor_get(v_a_6174_, 1);
v_isSharedCheck_6187_ = !lean_is_exclusive(v_a_6174_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6180_ = v_a_6174_;
v_isShared_6181_ = v_isSharedCheck_6187_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_tail_6178_);
lean_inc(v_head_6177_);
lean_dec(v_a_6174_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6187_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v_fst_6182_; lean_object* v___x_6184_; 
v_fst_6182_ = lean_ctor_get(v_head_6177_, 0);
lean_inc(v_fst_6182_);
lean_dec(v_head_6177_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 1, v_a_6175_);
lean_ctor_set(v___x_6180_, 0, v_fst_6182_);
v___x_6184_ = v___x_6180_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_fst_6182_);
lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_a_6175_);
v___x_6184_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
v_a_6174_ = v_tail_6178_;
v_a_6175_ = v___x_6184_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object* v_env_6188_, lean_object* v_constants_x3f_6189_, lean_object* v_cliOptions_6190_){
_start:
{
lean_object* v___y_6193_; 
if (lean_obj_tag(v_constants_x3f_6189_) == 0)
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
lean_inc_ref(v_env_6188_);
v___x_6196_ = l_Lean_Environment_constants(v_env_6188_);
v___x_6197_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v___x_6196_);
lean_dec_ref(v___x_6196_);
v___x_6198_ = lean_box(0);
v___x_6199_ = l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(v___x_6197_, v___x_6198_);
v___x_6200_ = l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(v___x_6199_, v___x_6198_);
v___y_6193_ = v___x_6200_;
goto v___jp_6192_;
}
else
{
lean_object* v_val_6201_; 
v_val_6201_ = lean_ctor_get(v_constants_x3f_6189_, 0);
lean_inc(v_val_6201_);
lean_dec_ref_known(v_constants_x3f_6189_, 1);
v___y_6193_ = v_val_6201_;
goto v___jp_6192_;
}
v___jp_6192_:
{
lean_object* v___f_6194_; lean_object* v___x_6195_; 
lean_inc_ref(v_env_6188_);
v___f_6194_ = lean_alloc_closure((void*)(l_LeanExport_dumpEnv___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6194_, 0, v_env_6188_);
lean_closure_set(v___f_6194_, 1, v_cliOptions_6190_);
lean_closure_set(v___f_6194_, 2, v___y_6193_);
v___x_6195_ = l_LeanExport_M_run___redArg(v_env_6188_, v___f_6194_);
return v___x_6195_;
}
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object* v_env_6202_, lean_object* v_constants_x3f_6203_, lean_object* v_cliOptions_6204_, lean_object* v_a_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l_LeanExport_dumpEnv(v_env_6202_, v_constants_x3f_6203_, v_cliOptions_6204_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object* v_as_6207_, lean_object* v_as_x27_6208_, lean_object* v_b_6209_, lean_object* v_a_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6208_, v_b_6209_, v___y_6211_, v___y_6212_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object* v_as_6215_, lean_object* v_as_x27_6216_, lean_object* v_b_6217_, lean_object* v_a_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_){
_start:
{
lean_object* v_res_6222_; 
v_res_6222_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6215_, v_as_x27_6216_, v_b_6217_, v_a_6218_, v___y_6219_, v___y_6220_);
lean_dec_ref(v___y_6219_);
lean_dec(v_as_x27_6216_);
lean_dec(v_as_6215_);
return v_res_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object* v_00_u03b2_6223_, lean_object* v_m_6224_){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6224_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object* v_00_u03b2_6226_, lean_object* v_m_6227_){
_start:
{
lean_object* v_res_6228_; 
v_res_6228_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(v_00_u03b2_6226_, v_m_6227_);
lean_dec_ref(v_m_6227_);
return v_res_6228_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object* v_00_u03b2_6229_, lean_object* v_00_u03c3_6230_, lean_object* v_f_6231_, lean_object* v_init_6232_, lean_object* v_m_6233_){
_start:
{
lean_object* v___x_6234_; 
v___x_6234_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6231_, v_init_6232_, v_m_6233_);
return v___x_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6235_, lean_object* v_00_u03c3_6236_, lean_object* v_f_6237_, lean_object* v_init_6238_, lean_object* v_m_6239_){
_start:
{
lean_object* v_res_6240_; 
v_res_6240_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(v_00_u03b2_6235_, v_00_u03c3_6236_, v_f_6237_, v_init_6238_, v_m_6239_);
lean_dec_ref(v_m_6239_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_6241_, lean_object* v_00_u03c3_6242_, lean_object* v_f_6243_, lean_object* v_x_6244_, lean_object* v_x_6245_){
_start:
{
lean_object* v___x_6246_; 
v___x_6246_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6243_, v_x_6244_, v_x_6245_);
return v___x_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_6247_, lean_object* v_00_u03b2_6248_, lean_object* v_map_6249_, lean_object* v_f_6250_, lean_object* v_init_6251_){
_start:
{
lean_object* v___x_6252_; 
v___x_6252_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6249_, v_f_6250_, v_init_6251_);
return v___x_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_6253_, lean_object* v_00_u03b2_6254_, lean_object* v_map_6255_, lean_object* v_f_6256_, lean_object* v_init_6257_){
_start:
{
lean_object* v_res_6258_; 
v_res_6258_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(v_00_u03c3_6253_, v_00_u03b2_6254_, v_map_6255_, v_f_6256_, v_init_6257_);
lean_dec_ref(v_map_6255_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_6259_, lean_object* v_00_u03c3_6260_, lean_object* v_f_6261_, lean_object* v_as_6262_, size_t v_i_6263_, size_t v_stop_6264_, lean_object* v_b_6265_){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6261_, v_as_6262_, v_i_6263_, v_stop_6264_, v_b_6265_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_6267_, lean_object* v_00_u03c3_6268_, lean_object* v_f_6269_, lean_object* v_as_6270_, lean_object* v_i_6271_, lean_object* v_stop_6272_, lean_object* v_b_6273_){
_start:
{
size_t v_i_boxed_6274_; size_t v_stop_boxed_6275_; lean_object* v_res_6276_; 
v_i_boxed_6274_ = lean_unbox_usize(v_i_6271_);
lean_dec(v_i_6271_);
v_stop_boxed_6275_ = lean_unbox_usize(v_stop_6272_);
lean_dec(v_stop_6272_);
v_res_6276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(v_00_u03b2_6267_, v_00_u03c3_6268_, v_f_6269_, v_as_6270_, v_i_boxed_6274_, v_stop_boxed_6275_, v_b_6273_);
lean_dec_ref(v_as_6270_);
return v_res_6276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_map_6277_, lean_object* v_f_6278_, lean_object* v_init_6279_){
_start:
{
lean_object* v___x_6280_; 
v___x_6280_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6278_, v_map_6277_, v_init_6279_);
return v___x_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_map_6281_, lean_object* v_f_6282_, lean_object* v_init_6283_){
_start:
{
lean_object* v_res_6284_; 
v_res_6284_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(v_map_6281_, v_f_6282_, v_init_6283_);
lean_dec_ref(v_map_6281_);
return v_res_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_6285_, lean_object* v_00_u03b2_6286_, lean_object* v_map_6287_, lean_object* v_f_6288_, lean_object* v_init_6289_){
_start:
{
lean_object* v___x_6290_; 
v___x_6290_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6288_, v_map_6287_, v_init_6289_);
return v___x_6290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_6291_, lean_object* v_00_u03b2_6292_, lean_object* v_map_6293_, lean_object* v_f_6294_, lean_object* v_init_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(v_00_u03c3_6291_, v_00_u03b2_6292_, v_map_6293_, v_f_6294_, v_init_6295_);
lean_dec_ref(v_map_6293_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03c3_6297_, lean_object* v_00_u03b1_6298_, lean_object* v_00_u03b2_6299_, lean_object* v_f_6300_, lean_object* v_x_6301_, lean_object* v_x_6302_){
_start:
{
lean_object* v___x_6303_; 
v___x_6303_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6300_, v_x_6301_, v_x_6302_);
return v___x_6303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03c3_6304_, lean_object* v_00_u03b1_6305_, lean_object* v_00_u03b2_6306_, lean_object* v_f_6307_, lean_object* v_x_6308_, lean_object* v_x_6309_){
_start:
{
lean_object* v_res_6310_; 
v_res_6310_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(v_00_u03c3_6304_, v_00_u03b1_6305_, v_00_u03b2_6306_, v_f_6307_, v_x_6308_, v_x_6309_);
lean_dec_ref(v_x_6308_);
return v_res_6310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_6311_, lean_object* v_00_u03b2_6312_, lean_object* v_00_u03c3_6313_, lean_object* v_f_6314_, lean_object* v_as_6315_, size_t v_i_6316_, size_t v_stop_6317_, lean_object* v_b_6318_){
_start:
{
lean_object* v___x_6319_; 
v___x_6319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6314_, v_as_6315_, v_i_6316_, v_stop_6317_, v_b_6318_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_6320_, lean_object* v_00_u03b2_6321_, lean_object* v_00_u03c3_6322_, lean_object* v_f_6323_, lean_object* v_as_6324_, lean_object* v_i_6325_, lean_object* v_stop_6326_, lean_object* v_b_6327_){
_start:
{
size_t v_i_boxed_6328_; size_t v_stop_boxed_6329_; lean_object* v_res_6330_; 
v_i_boxed_6328_ = lean_unbox_usize(v_i_6325_);
lean_dec(v_i_6325_);
v_stop_boxed_6329_ = lean_unbox_usize(v_stop_6326_);
lean_dec(v_stop_6326_);
v_res_6330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(v_00_u03b1_6320_, v_00_u03b2_6321_, v_00_u03c3_6322_, v_f_6323_, v_as_6324_, v_i_boxed_6328_, v_stop_boxed_6329_, v_b_6327_);
lean_dec_ref(v_as_6324_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object* v_00_u03c3_6331_, lean_object* v_00_u03b1_6332_, lean_object* v_00_u03b2_6333_, lean_object* v_f_6334_, lean_object* v_keys_6335_, lean_object* v_vals_6336_, lean_object* v_heq_6337_, lean_object* v_i_6338_, lean_object* v_acc_6339_){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6334_, v_keys_6335_, v_vals_6336_, v_i_6338_, v_acc_6339_);
return v___x_6340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03c3_6341_, lean_object* v_00_u03b1_6342_, lean_object* v_00_u03b2_6343_, lean_object* v_f_6344_, lean_object* v_keys_6345_, lean_object* v_vals_6346_, lean_object* v_heq_6347_, lean_object* v_i_6348_, lean_object* v_acc_6349_){
_start:
{
lean_object* v_res_6350_; 
v_res_6350_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(v_00_u03c3_6341_, v_00_u03b1_6342_, v_00_u03b2_6343_, v_f_6344_, v_keys_6345_, v_vals_6346_, v_heq_6347_, v_i_6348_, v_acc_6349_);
lean_dec_ref(v_vals_6346_);
lean_dec_ref(v_keys_6345_);
return v_res_6350_;
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
